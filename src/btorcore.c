/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2017 Armin Biere.
 *  Copyright (C) 2012-2020 Mathias Preiner.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"

#include <limits.h>

#include "btorabort.h"
#ifndef NDEBUG
#include "btorchkfailed.h"
#include "btorchkmodel.h"
#endif
#include "btorclone.h"
#include "btorconfig.h"
#include "btordbg.h"
#include "btorexp.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btoropt.h"
#include "btorrewrite.h"
#include "btorslvaigprop.h"
#include "btorslvfun.h"
#include "btorslvprop.h"
#include "btorslvquant.h"
#include "btorslvsls.h"
#include "btorsubst.h"
#include "preprocess/btorpreprocess.h"
#include "preprocess/btorvarsubst.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

#define BTOR_INIT_UNIQUE_TABLE(mm, table) \
  do                                      \
  {                                       \
    assert (mm);                          \
    (table).size         = 1;             \
    (table).num_elements = 0;             \
    BTOR_CNEW (mm, (table).chains);       \
  } while (0)

#define BTOR_RELEASE_UNIQUE_TABLE(mm, table)         \
  do                                                 \
  {                                                  \
    assert (mm);                                     \
    BTOR_DELETEN (mm, (table).chains, (table).size); \
  } while (0)

#define BTOR_INIT_SORT_UNIQUE_TABLE(mm, table) \
  do                                           \
  {                                            \
    BTOR_INIT_UNIQUE_TABLE (mm, table);        \
    table.mm = mm;                             \
    BTOR_INIT_STACK (mm, table.id2sort);       \
    BTOR_PUSH_STACK (table.id2sort, 0);        \
  } while (0)

#define BTOR_RELEASE_SORT_UNIQUE_TABLE(mm, table) \
  do                                              \
  {                                               \
    BTOR_RELEASE_UNIQUE_TABLE (mm, table);        \
    BTOR_RELEASE_STACK (table.id2sort);           \
  } while (0)

#define BTOR_COND_INVERT_AIG_NODE(exp, aig) \
  ((BtorAIG *) (((uint32_t long int) (exp) &1ul) ^ ((uint32_t long int) (aig))))

#define BTOR_AIGVEC_NODE(btor, exp)                                     \
  (btor_node_is_inverted (exp)                                          \
       ? btor_aigvec_not ((btor)->avmgr, btor_node_real_addr (exp)->av) \
       : btor_aigvec_copy ((btor)->avmgr, exp->av))

/*------------------------------------------------------------------------*/

static BtorAIG *exp_to_aig (Btor *, BtorNode *);

/*------------------------------------------------------------------------*/

enum BtorSubstCompKind
{
  BTOR_SUBST_COMP_ULT_KIND,
  BTOR_SUBST_COMP_ULTE_KIND,
  BTOR_SUBST_COMP_UGT_KIND,
  BTOR_SUBST_COMP_UGTE_KIND
};

typedef enum BtorSubstCompKind BtorSubstCompKind;

/*------------------------------------------------------------------------*/

void
btor_init_substitutions (Btor *btor)
{
  assert (btor);
  assert (!btor->substitutions);

  btor->substitutions =
      btor_hashptr_table_new (btor->mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
}

void
btor_delete_substitutions (Btor *btor)
{
  assert (btor);

  if (!btor->substitutions) return;

  BtorNode *cur;
  BtorPtrHashTableIterator it;

  btor_iter_hashptr_init (&it, btor->substitutions);
  while (btor_iter_hashptr_has_next (&it))
  {
    btor_node_release (btor, (BtorNode *) it.bucket->data.as_ptr);
    cur = btor_iter_hashptr_next (&it);
    btor_node_release (btor, cur);
  }

  btor_hashptr_table_delete (btor->substitutions);
  btor->substitutions = 0;
}

BtorNode *
btor_find_substitution (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *result = 0;
  BtorPtrHashBucket *b;

  if (!btor->substitutions) return 0;

  while (1)
  {
    b = btor_hashptr_table_get (btor->substitutions, btor_node_real_addr (exp));
    if (!b) break;
    result = btor_node_cond_invert (exp, (BtorNode *) b->data.as_ptr);
    exp    = result;
  }

  return result;
}

#ifndef NDEBUG
static bool
substitution_cycle_check_dbg (Btor *btor, BtorNode *exp, BtorNode *subst)
{
  uint32_t i;
  bool iscycle = false;
  BtorMemMgr *mm;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;

  mm    = btor->mm;
  exp   = btor_node_real_addr (exp);
  cache = btor_hashint_table_new (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, subst);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id)) continue;

    if (cur == exp)
    {
      iscycle = true;
      break;
    }

    btor_hashint_table_add (cache, cur->id);

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }
  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (cache);
  return !iscycle;
}
#endif

void
btor_insert_substitution (Btor *btor,
                          BtorNode *exp,
                          BtorNode *subst,
                          bool update)
{
  assert (btor);
  assert (exp);
  assert (subst);
  assert (btor->substitutions);
  assert (btor_node_get_sort_id (exp) == btor_node_get_sort_id (subst));
  assert (!btor_node_is_simplified (exp));

  BtorNode *simp;
  BtorPtrHashBucket *b;
  exp = btor_node_real_addr (exp);

  if (exp == btor_node_real_addr (subst)) return;

  assert (substitution_cycle_check_dbg (btor, exp, subst));

  b = btor_hashptr_table_get (btor->substitutions, exp);
  if (update && b)
  {
    assert (b->data.as_ptr);
    /* release data of current bucket */
    btor_node_release (btor, (BtorNode *) b->data.as_ptr);
    btor_hashptr_table_remove (btor->substitutions, exp, 0, 0);
    /* release key of current bucket */
    btor_node_release (btor, exp);
  }
  else if (b)
  {
    assert ((BtorNode *) b->data.as_ptr == subst);
    /* substitution already inserted */
    return;
  }

  simp = btor_find_substitution (btor, subst);

  if (simp) subst = simp;

  assert (!btor_hashptr_table_get (btor->substitutions,
                                   btor_node_real_addr (subst)));

  if (exp == btor_node_real_addr (subst)) return;

  btor_hashptr_table_add (btor->substitutions, btor_node_copy (btor, exp))
      ->data.as_ptr = btor_node_copy (btor, subst);
}

/*------------------------------------------------------------------------*/

const char *
btor_version (const Btor *btor)
{
  assert (btor);
  (void) btor;
  return BTOR_VERSION;
}

const char *
btor_git_id (const Btor *btor)
{
  assert (btor);
  (void) btor;
  return BTOR_GIT_ID;
}

BtorAIGMgr *
btor_get_aig_mgr (const Btor *btor)
{
  assert (btor);
  return btor_aigvec_get_aig_mgr (btor->avmgr);
}

BtorSATMgr *
btor_get_sat_mgr (const Btor *btor)
{
  assert (btor);
  return btor_aig_get_sat_mgr (btor_get_aig_mgr (btor));
}

void
btor_reset_time (Btor *btor)
{
  assert (btor);
  BTOR_CLR (&btor->time);
}

void
btor_reset_stats (Btor *btor)
{
  assert (btor);
#ifndef NDEBUG
  if (btor->stats.rw_rules_applied)
    btor_hashptr_table_delete (btor->stats.rw_rules_applied);
#endif
  BTOR_CLR (&btor->stats);
#ifndef NDEBUG
  assert (!btor->stats.rw_rules_applied);
  btor->stats.rw_rules_applied = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
#endif
}

static uint32_t
constraints_stats_changes (Btor *btor)
{
  uint32_t res;

  if (btor->stats.oldconstraints.varsubst && !btor->varsubst_constraints->count)
    return UINT32_MAX;

  if (btor->stats.oldconstraints.embedded && !btor->embedded_constraints->count)
    return UINT32_MAX;

  if (btor->stats.oldconstraints.unsynthesized
      && !btor->unsynthesized_constraints->count)
    return UINT32_MAX;

  res = btor->stats.oldconstraints.varsubst >= btor->varsubst_constraints->count
            ? btor->stats.oldconstraints.varsubst
                  - btor->varsubst_constraints->count
            : btor->varsubst_constraints->count
                  - btor->stats.oldconstraints.varsubst;
  res +=
      btor->stats.oldconstraints.embedded >= btor->embedded_constraints->count
          ? btor->stats.oldconstraints.embedded
                - btor->embedded_constraints->count
          : btor->embedded_constraints->count
                - btor->stats.oldconstraints.embedded;
  res += btor->stats.oldconstraints.unsynthesized
                 >= btor->unsynthesized_constraints->count
             ? btor->stats.oldconstraints.unsynthesized
                   - btor->unsynthesized_constraints->count
             : btor->unsynthesized_constraints->count
                   - btor->stats.oldconstraints.unsynthesized;
  res += btor->stats.oldconstraints.synthesized
                 >= btor->synthesized_constraints->count
             ? btor->stats.oldconstraints.synthesized
                   - btor->synthesized_constraints->count
             : btor->synthesized_constraints->count
                   - btor->stats.oldconstraints.synthesized;

  return res;
}

static void
report_constraint_stats (Btor *btor, bool force)
{
  uint32_t changes;

  if (!force)
  {
    if (btor_opt_get (btor, BTOR_OPT_VERBOSITY) <= 0) return;

    changes = constraints_stats_changes (btor);

    if (btor_opt_get (btor, BTOR_OPT_VERBOSITY) == 1 && changes < 100000)
      return;

    if (btor_opt_get (btor, BTOR_OPT_VERBOSITY) == 2 && changes < 1000) return;

    if (btor_opt_get (btor, BTOR_OPT_VERBOSITY) == 3 && changes < 10) return;

    if (!changes) return;
  }

  BTOR_MSG (btor->msg,
            1,
            "%d/%d/%d/%d constraints %d/%d/%d/%d %.1f MB",
            btor->stats.constraints.varsubst,
            btor->stats.constraints.embedded,
            btor->stats.constraints.unsynthesized,
            btor->stats.constraints.synthesized,
            btor->varsubst_constraints->count,
            btor->embedded_constraints->count,
            btor->unsynthesized_constraints->count,
            btor->synthesized_constraints->count,
            btor->mm->allocated / (double) (1 << 20));

  btor->stats.oldconstraints.varsubst = btor->varsubst_constraints->count;
  btor->stats.oldconstraints.embedded = btor->embedded_constraints->count;
  btor->stats.oldconstraints.unsynthesized =
      btor->unsynthesized_constraints->count;
  btor->stats.oldconstraints.synthesized = btor->synthesized_constraints->count;
}

/* we do not count proxies */
static uint32_t
number_of_ops (Btor *btor)
{
  int32_t i, result;
  assert (btor);

  result = 0;
  for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++) result += btor->ops[i].cur;

  return result;
}

#ifdef BTOR_TIME_STATISTICS
static double
percent (double a, double b)
{
  return b ? 100.0 * a / b : 0.0;
}
#endif

void
btor_print_stats (Btor *btor)
{
  uint32_t i, num_final_ops;
  uint32_t verbosity;

  if (!btor) return;

  verbosity = btor_opt_get (btor, BTOR_OPT_VERBOSITY);

  report_constraint_stats (btor, true);

  BTOR_MSG (btor->msg, 1, "%u assumptions", btor->assumptions->count);

  if (verbosity > 0)
  {
    BTOR_MSG (btor->msg, 1, "");
    BTOR_MSG (btor->msg, 2, "%5d max rec. RW", btor->stats.max_rec_rw_calls);
    BTOR_MSG (btor->msg,
              2,
              "%5lld number of expressions ever created",
              btor->stats.expressions);
    num_final_ops = number_of_ops (btor);
    BTOR_MSG (btor->msg, 2, "%5d number of final expressions", num_final_ops);
    assert (sizeof g_btor_op2str / sizeof *g_btor_op2str == BTOR_NUM_OPS_NODE);

    BTOR_MSG (btor->msg,
              1,
              "%.2f MB allocated for nodes",
              btor->stats.node_bytes_alloc / (double) (1 << 20));
    if (num_final_ops > 0)
      for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++)
        if (btor->ops[i].cur || btor->ops[i].max)
          BTOR_MSG (btor->msg,
                    2,
                    " %s: %d max %d",
                    g_btor_op2str[i],
                    btor->ops[i].cur,
                    btor->ops[i].max);
    BTOR_MSG (btor->msg, 1, "");
  }

  if (btor_opt_get (btor, BTOR_OPT_UCOPT))
  {
    BTOR_MSG (
        btor->msg, 1, "%5d unconstrained bv props", btor->stats.bv_uc_props);
    BTOR_MSG (btor->msg,
              1,
              "%5d unconstrained array props",
              btor->stats.fun_uc_props);
    BTOR_MSG (btor->msg,
              1,
              "%5d unconstrained parameterized props",
              btor->stats.param_uc_props);
  }
  BTOR_MSG (btor->msg,
            1,
            "%5d variable substitutions",
            btor->stats.var_substitutions);
  BTOR_MSG (btor->msg,
            1,
            "%5d uninterpreted function substitutions",
            btor->stats.uf_substitutions);
  BTOR_MSG (btor->msg,
            1,
            "%5d embedded constraint substitutions",
            btor->stats.ec_substitutions);
  BTOR_MSG (btor->msg,
            1,
            "%5d synthesized nodes rewritten",
            btor->stats.rewrite_synth);

  BTOR_MSG (btor->msg,
            1,
            "%5d linear constraint equations",
            btor->stats.linear_equations);
  BTOR_MSG (btor->msg,
            1,
            "%5d gaussian eliminations in linear equations",
            btor->stats.gaussian_eliminations);
  BTOR_MSG (btor->msg,
            1,
            "%5d eliminated sliced variables",
            btor->stats.eliminated_slices);
  BTOR_MSG (btor->msg,
            1,
            "%5d extracted skeleton constraints",
            btor->stats.skeleton_constraints);
  BTOR_MSG (
      btor->msg, 1, "%5d and normalizations", btor->stats.ands_normalized);
  BTOR_MSG (
      btor->msg, 1, "%5d add normalizations", btor->stats.adds_normalized);
  BTOR_MSG (
      btor->msg, 1, "%5d mul normalizations", btor->stats.muls_normalized);
  BTOR_MSG (btor->msg, 1, "%5lld lambdas merged", btor->stats.lambdas_merged);
  BTOR_MSG (btor->msg,
            1,
            "%5d static apply propagations over lambdas",
            btor->stats.prop_apply_lambda);
  BTOR_MSG (btor->msg,
            1,
            "%5d static apply propagations over updates",
            btor->stats.prop_apply_update);
  BTOR_MSG (
      btor->msg, 1, "%5lld beta reductions", btor->stats.beta_reduce_calls);
  BTOR_MSG (btor->msg, 1, "%5lld clone calls", btor->stats.clone_calls);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "rewrite rule cache");
  BTOR_MSG (btor->msg, 1, "  %lld cached (add) ", btor->rw_cache->num_add);
  BTOR_MSG (btor->msg, 1, "  %lld cached (get)", btor->rw_cache->num_get);
  BTOR_MSG (btor->msg, 1, "  %lld updated", btor->rw_cache->num_update);
  BTOR_MSG (btor->msg, 1, "  %lld removed (gc)", btor->rw_cache->num_remove);
  BTOR_MSG (btor->msg,
            1,
            "  %.2f MB cache",
            (btor->rw_cache->cache->count * sizeof (BtorRwCacheTuple)
             + btor->rw_cache->cache->count * sizeof (BtorPtrHashBucket)
             + btor->rw_cache->cache->size * sizeof (BtorPtrHashBucket *))
                / (double) (1 << 20));

#ifndef NDEBUG
  BtorPtrHashTableIterator it;
  char *rule;
  int32_t num = 0;
  BTOR_MSG (btor->msg, 1, "applied rewriting rules:");
  if (btor->stats.rw_rules_applied->count == 0)
    BTOR_MSG (btor->msg, 1, "  none");
  else
  {
    btor_iter_hashptr_init (&it, btor->stats.rw_rules_applied);
    while (btor_iter_hashptr_has_next (&it))
    {
      num  = it.bucket->data.as_int;
      rule = btor_iter_hashptr_next (&it);
      BTOR_MSG (btor->msg, 1, "  %5d %s", num, rule);
    }
  }
#endif

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "bit blasting statistics:");
  BTOR_MSG (btor->msg,
            1,
            "  %7lld AIG vectors (%lld max)",
            btor->avmgr ? btor->avmgr->cur_num_aigvecs : 0,
            btor->avmgr ? btor->avmgr->max_num_aigvecs : 0);
  BTOR_MSG (btor->msg,
            1,
            "  %7lld AIG ANDs (%lld max)",
            btor->avmgr ? btor->avmgr->amgr->cur_num_aigs : 0,
            btor->avmgr ? btor->avmgr->amgr->max_num_aigs : 0);
  BTOR_MSG (btor->msg,
            1,
            "  %7lld AIG variables",
            btor->avmgr ? btor->avmgr->amgr->max_num_aig_vars : 0);
  BTOR_MSG (btor->msg,
            1,
            "  %7lld CNF variables",
            btor->avmgr ? btor->avmgr->amgr->num_cnf_vars : 0);
  BTOR_MSG (btor->msg,
            1,
            "  %7lld CNF clauses",
            btor->avmgr ? btor->avmgr->amgr->num_cnf_clauses : 0);
  BTOR_MSG (btor->msg,
            1,
            "  %7lld CNF literals",
            btor->avmgr ? btor->avmgr->amgr->num_cnf_literals : 0);

  if (btor->slv) btor->slv->api.print_stats (btor->slv);

#ifdef BTOR_TIME_STATISTICS
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "%.2f seconds beta-reduction", btor->time.beta);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds synthesize expressions",
            btor->time.synth_exp);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds determining failed assumptions",
            btor->time.failed);
  BTOR_MSG (btor->msg, 1, "%.2f seconds cloning", btor->time.cloning);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds substitute and rebuild",
            btor->time.subst_rebuild);
  if (btor_opt_get (btor, BTOR_OPT_MODEL_GEN))
    BTOR_MSG (
        btor->msg, 1, "%.2f seconds model generation", btor->time.model_gen);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "%.2f seconds solving", btor->time.sat);
  BTOR_MSG (
      btor->msg, 1, "  %.2f seconds rewriting engine", btor->time.simplify);
  BTOR_MSG (btor->msg,
            1,
            "    %.2f seconds variable substitution (%.0f%%)",
            btor->time.subst,
            percent (btor->time.subst, btor->time.simplify));
  BTOR_MSG (btor->msg, 1, "    %.2f seconds rewriting", btor->time.rewrite);
  BTOR_MSG (
      btor->msg, 1, "    %.2f seconds occurrence check", btor->time.occurrence);

  BTOR_MSG (btor->msg,
            1,
            "    %.2f seconds embedded substitution (%.0f%%)",
            btor->time.embedded,
            percent (btor->time.embedded, btor->time.simplify));

  if (btor_opt_get (btor, BTOR_OPT_ELIMINATE_SLICES))
    BTOR_MSG (btor->msg,
              1,
              "    %.2f seconds variable slicing (%.0f%%)",
              btor->time.slicing,
              percent (btor->time.slicing, btor->time.simplify));

#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  BTOR_MSG (btor->msg,
            1,
            "    %.2f seconds skeleton preprocessing (%.0f%%)",
            btor->time.skel,
            percent (btor->time.skel, btor->time.simplify));
#endif

  if (btor_opt_get (btor, BTOR_OPT_UCOPT))
    BTOR_MSG (btor->msg,
              1,
              "    %.2f seconds unconstrained optimization",
              btor->time.ucopt);

  if (btor_opt_get (btor, BTOR_OPT_EXTRACT_LAMBDAS))
    BTOR_MSG (btor->msg,
              1,
              "    %.2f seconds lambda extraction (%.0f%%)",
              btor->time.extract,
              percent (btor->time.extract, btor->time.simplify));

  if (btor_opt_get (btor, BTOR_OPT_MERGE_LAMBDAS))
    BTOR_MSG (btor->msg,
              1,
              "    %.2f seconds lambda merging (%.0f%%)",
              btor->time.merge,
              percent (btor->time.merge, btor->time.simplify));

  if (btor_opt_get (btor, BTOR_OPT_BETA_REDUCE))
    BTOR_MSG (btor->msg,
              1,
              "    %.2f seconds apply elimination (%.0f%%)",
              btor->time.elimapplies,
              percent (btor->time.elimapplies, btor->time.simplify));

  if (btor_opt_get (btor, BTOR_OPT_ACKERMANN))
    BTOR_MSG (btor->msg,
              1,
              "    %.2f seconds ackermann constraints (%.0f%%)",
              btor->time.ack,
              percent (btor->time.ack, btor->time.simplify));

  if (btor->slv) btor->slv->api.print_time_stats (btor->slv);
#endif

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (
      btor->msg, 1, "%.1f MB", btor->mm->maxallocated / (double) (1 << 20));
}

Btor *
btor_new (void)
{
  BtorMemMgr *mm;
  Btor *btor;

  mm = btor_mem_mgr_new ();
  BTOR_CNEW (mm, btor);

  btor->mm  = mm;
  btor->msg = btor_msg_new (btor);
  btor_set_msg_prefix (btor, "btor");

  BTOR_INIT_UNIQUE_TABLE (mm, btor->nodes_unique_table);
  BTOR_INIT_SORT_UNIQUE_TABLE (mm, btor->sorts_unique_table);
  BTOR_INIT_STACK (btor->mm, btor->nodes_id_table);
  BTOR_PUSH_STACK (btor->nodes_id_table, 0);
  BTOR_INIT_STACK (btor->mm, btor->functions_with_model);
  BTOR_INIT_STACK (btor->mm, btor->outputs);

  btor_opt_init_opts (btor);

  btor->avmgr = btor_aigvec_mgr_new (btor);

  btor_rng_init (&btor->rng, btor_opt_get (btor, BTOR_OPT_SEED));

  btor->bv_assignments  = btor_ass_new_bv_list (mm);
  btor->fun_assignments = btor_ass_new_fun_list (mm);

  btor->symbols = btor_hashptr_table_new (
      mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor->node2symbol =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);

  btor->inputs  = btor_hashptr_table_new (mm,
                                         (BtorHashPtr) btor_node_hash_by_id,
                                         (BtorCmpPtr) btor_node_compare_by_id);
  btor->bv_vars = btor_hashptr_table_new (mm,
                                          (BtorHashPtr) btor_node_hash_by_id,
                                          (BtorCmpPtr) btor_node_compare_by_id);
  btor->ufs     = btor_hashptr_table_new (mm,
                                      (BtorHashPtr) btor_node_hash_by_id,
                                      (BtorCmpPtr) btor_node_compare_by_id);
  btor->lambdas = btor_hashptr_table_new (mm,
                                          (BtorHashPtr) btor_node_hash_by_id,
                                          (BtorCmpPtr) btor_node_compare_by_id);
  btor->quantifiers =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->exists_vars =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->forall_vars =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->feqs = btor_hashptr_table_new (mm,
                                       (BtorHashPtr) btor_node_hash_by_id,
                                       (BtorCmpPtr) btor_node_compare_by_id);

  btor->valid_assignments = 1;

  btor->varsubst_constraints =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->embedded_constraints =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->unsynthesized_constraints =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->synthesized_constraints =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->assumptions =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->orig_assumptions =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  BTOR_INIT_STACK (mm, btor->failed_assumptions);
  btor->parameterized =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);

  BTOR_INIT_STACK (mm, btor->assertions);
  BTOR_INIT_STACK (mm, btor->assertions_trail);
  btor->assertions_cache = btor_hashint_table_new (mm);

#ifndef NDEBUG
  btor->stats.rw_rules_applied = btor_hashptr_table_new (
      mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
#endif

  btor->true_exp = btor_exp_true (btor);

  BTOR_CNEW (mm, btor->rw_cache);
  btor_rw_cache_init (btor->rw_cache, btor);

  return btor;
}

static int32_t
terminate_aux_btor (void *btor)
{
  assert (btor);

  int32_t res;
  Btor *bt;

  bt = (Btor *) btor;
  if (!bt->cbs.term.fun) return 0;
  if (bt->cbs.term.done) return 1;
  res = ((int32_t (*) (void *)) bt->cbs.term.fun) (bt->cbs.term.state);
  if (res) bt->cbs.term.done = res;
  return res;
}

int32_t
btor_terminate (Btor *btor)
{
  assert (btor);

  if (btor->cbs.term.termfun) return btor->cbs.term.termfun (btor);
  return 0;
}

void
btor_set_term (Btor *btor, int32_t (*fun) (void *), void *state)
{
  assert (btor);

  BtorSATMgr *smgr;

  btor->cbs.term.termfun = terminate_aux_btor;
  btor->cbs.term.fun     = fun;
  btor->cbs.term.state   = state;

  smgr = btor_get_sat_mgr (btor);
  btor_sat_mgr_set_term (smgr, terminate_aux_btor, btor);
}

static void
release_all_ext_exp_refs (Btor *btor)
{
  assert (btor);

  uint32_t i, cnt;
  BtorNode *exp;

  for (i = 1, cnt = BTOR_COUNT_STACK (btor->nodes_id_table); i <= cnt; i++)
  {
    if (!(exp = BTOR_PEEK_STACK (btor->nodes_id_table, cnt - i))) continue;
    if (exp->ext_refs)
    {
      assert (exp->ext_refs <= exp->refs);
      exp->refs = exp->refs - exp->ext_refs + 1;
      btor->external_refs -= exp->ext_refs;
      assert (exp->refs > 0);
      exp->ext_refs = 0;
      btor_node_release (btor, exp);
    }
  }
}

static void
release_all_ext_sort_refs (Btor *btor)
{
  assert (btor);

  uint32_t i, cnt;
  BtorSort *sort;

  cnt = BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort);
  for (i = 1; i <= cnt; i++)
  {
    sort = BTOR_PEEK_STACK (btor->sorts_unique_table.id2sort, cnt - i);
    if (!sort) continue;
    assert (sort->refs);
    assert (sort->ext_refs <= sort->refs);
    sort->refs = sort->refs - sort->ext_refs + 1;
    btor->external_refs -= sort->ext_refs;
    assert (sort->refs > 0);
    sort->ext_refs = 0;
    btor_sort_release (btor, sort->id);
  }
}

void
btor_release_all_ext_refs (Btor *btor)
{
  release_all_ext_exp_refs (btor);
  release_all_ext_sort_refs (btor);
}

void
btor_delete_varsubst_constraints (Btor *btor)
{
  BtorPtrHashTableIterator it;
  btor_iter_hashptr_init (&it, btor->varsubst_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    btor_node_release (btor, it.bucket->data.as_ptr);
    btor_node_release (btor, btor_iter_hashptr_next (&it));
  }
  btor_hashptr_table_delete (btor->varsubst_constraints);
}

void
btor_delete (Btor *btor)
{
  assert (btor);

  uint32_t i, cnt;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorNode *exp;
  BtorPtrHashTableIterator it;

  mm = btor->mm;
  btor_rng_delete (&btor->rng);

  if (btor->slv) btor->slv->api.delet (btor->slv);

  if (btor->parse_error_msg) btor_mem_freestr (mm, btor->parse_error_msg);

  btor_ass_delete_bv_list (
      btor->bv_assignments,
      btor_opt_get (btor, BTOR_OPT_AUTO_CLEANUP)
          || btor_opt_get (btor, BTOR_OPT_AUTO_CLEANUP_INTERNAL));
  btor_ass_delete_fun_list (
      btor->fun_assignments,
      btor_opt_get (btor, BTOR_OPT_AUTO_CLEANUP)
          || btor_opt_get (btor, BTOR_OPT_AUTO_CLEANUP_INTERNAL));

  btor_delete_varsubst_constraints (btor);

  btor_iter_hashptr_init (&it, btor->inputs);
  btor_iter_hashptr_queue (&it, btor->embedded_constraints);
  btor_iter_hashptr_queue (&it, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->assumptions);
  btor_iter_hashptr_queue (&it, btor->orig_assumptions);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (btor, btor_iter_hashptr_next (&it));

  btor_hashptr_table_delete (btor->inputs);
  btor_hashptr_table_delete (btor->embedded_constraints);
  btor_hashptr_table_delete (btor->unsynthesized_constraints);
  btor_hashptr_table_delete (btor->synthesized_constraints);
  btor_hashptr_table_delete (btor->assumptions);
  btor_hashptr_table_delete (btor->orig_assumptions);
  for (i = 0; i < BTOR_COUNT_STACK (btor->failed_assumptions); i++)
  {
    if (BTOR_PEEK_STACK (btor->failed_assumptions, i))
      btor_node_release (btor, BTOR_PEEK_STACK (btor->failed_assumptions, i));
  }
  BTOR_RELEASE_STACK (btor->failed_assumptions);

  for (i = 0; i < BTOR_COUNT_STACK (btor->assertions); i++)
    btor_node_release (btor, BTOR_PEEK_STACK (btor->assertions, i));
  BTOR_RELEASE_STACK (btor->assertions);
  BTOR_RELEASE_STACK (btor->assertions_trail);
  btor_hashint_table_delete (btor->assertions_cache);

  btor_model_delete (btor);
  btor_node_release (btor, btor->true_exp);

  for (i = 0; i < BTOR_COUNT_STACK (btor->functions_with_model); i++)
    btor_node_release (btor, BTOR_PEEK_STACK (btor->functions_with_model, i));
  BTOR_RELEASE_STACK (btor->functions_with_model);

  for (i = 0; i < BTOR_COUNT_STACK (btor->outputs); i++)
    btor_node_release (btor, BTOR_PEEK_STACK (btor->outputs, i));
  BTOR_RELEASE_STACK (btor->outputs);

  BTOR_INIT_STACK (mm, stack);
  /* copy lambdas and push onto stack since btor->lambdas does not hold a
   * reference and they may get released if btor_node_lambda_delete_static_rho
   * is called */
  btor_iter_hashptr_init (&it, btor->lambdas);
  while (btor_iter_hashptr_has_next (&it))
  {
    exp = btor_iter_hashptr_next (&it);
    BTOR_PUSH_STACK (stack, btor_node_copy (btor, exp));
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    exp = BTOR_POP_STACK (stack);
    btor_node_lambda_delete_static_rho (btor, exp);
    btor_node_release (btor, exp);
  }
  BTOR_RELEASE_STACK (stack);

  if (btor_opt_get (btor, BTOR_OPT_AUTO_CLEANUP) && btor->external_refs)
    release_all_ext_exp_refs (btor);

  if (btor_opt_get (btor, BTOR_OPT_AUTO_CLEANUP_INTERNAL))
  {
    cnt = BTOR_COUNT_STACK (btor->nodes_id_table);
    for (i = 1; i <= cnt; i++)
    {
      exp = BTOR_PEEK_STACK (btor->nodes_id_table, cnt - i);
      if (!exp) continue;
      if (btor_node_is_simplified (exp)) exp->simplified = 0;
    }
    for (i = 1; i <= cnt; i++)
    {
      exp = BTOR_PEEK_STACK (btor->nodes_id_table, cnt - i);
      if (!exp) continue;
      assert (exp->refs);
      exp->refs = 1;
      btor->external_refs -= exp->ext_refs;
      exp->ext_refs = 0;
      btor_node_release (btor, exp);
      assert (!BTOR_PEEK_STACK (btor->nodes_id_table, cnt - i));
    }
  }

  if (btor_opt_get (btor, BTOR_OPT_AUTO_CLEANUP) && btor->external_refs)
    release_all_ext_sort_refs (btor);

  assert (getenv ("BTORLEAK") || btor->external_refs == 0);

#ifndef NDEBUG
  bool node_leak = false;
  BtorNode *cur;
  /* we need to check id_table here as not all nodes are in the unique table */
  for (i = 0; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
    if (cur)
    {
      BTORLOG (1,
               "  unreleased node: %s (%d)",
               btor_util_node2string (cur),
               cur->refs);
      node_leak = true;
    }
  }
  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKEXP") || !node_leak);
#endif
  BTOR_RELEASE_UNIQUE_TABLE (mm, btor->nodes_unique_table);
  BTOR_RELEASE_STACK (btor->nodes_id_table);

  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKSORT")
          || btor->sorts_unique_table.num_elements == 0);
  BTOR_RELEASE_SORT_UNIQUE_TABLE (mm, btor->sorts_unique_table);

  btor_hashptr_table_delete (btor->node2symbol);
  btor_iter_hashptr_init (&it, btor->symbols);
  while (btor_iter_hashptr_has_next (&it))
    btor_mem_freestr (btor->mm, (char *) btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (btor->symbols);

  btor_hashptr_table_delete (btor->bv_vars);
  btor_hashptr_table_delete (btor->ufs);
  btor_hashptr_table_delete (btor->lambdas);
  btor_hashptr_table_delete (btor->quantifiers);
  assert (btor->exists_vars->count == 0);
  btor_hashptr_table_delete (btor->exists_vars);
  assert (btor->forall_vars->count == 0);
  btor_hashptr_table_delete (btor->forall_vars);
  btor_hashptr_table_delete (btor->feqs);
  btor_hashptr_table_delete (btor->parameterized);
#ifndef NDEBUG
  btor_hashptr_table_delete (btor->stats.rw_rules_applied);
#endif

  if (btor->avmgr) btor_aigvec_mgr_delete (btor->avmgr);
  btor_opt_delete_opts (btor);

  btor_rw_cache_delete (btor->rw_cache);
  BTOR_DELETE (mm, btor->rw_cache);

  assert (btor->rec_rw_calls == 0);
  btor_msg_delete (btor->msg);
  BTOR_DELETE (mm, btor);
  btor_mem_mgr_delete (mm);
}

void
btor_set_msg_prefix (Btor *btor, const char *prefix)
{
  assert (btor);

  btor_mem_freestr (btor->mm, btor->msg->prefix);
  btor->msg->prefix =
      prefix ? btor_mem_strdup (btor->mm, prefix) : (char *) prefix;
}

/* synthesizes unsynthesized constraints and updates constraints tables. */
void
btor_process_unsynthesized_constraints (Btor *btor)
{
  assert (btor);
  assert (!btor->inconsistent);

  BtorPtrHashTable *uc, *sc;
  BtorPtrHashBucket *bucket;
  BtorNode *cur;
  BtorAIG *aig;
  BtorAIGMgr *amgr;

  uc   = btor->unsynthesized_constraints;
  sc   = btor->synthesized_constraints;
  amgr = btor_get_aig_mgr (btor);

  while (uc->count > 0)
  {
    bucket = uc->first;
    assert (bucket);
    cur = (BtorNode *) bucket->key;

#if 0
#ifndef NDEBUG
      if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2)
	{
	  BtorNode * real_cur = btor_node_real_addr (cur);
	  if (btor_node_is_bv_eq (real_cur))
	    {
	      BtorNode * left = real_cur->e[0];
	      BtorNode * right = real_cur->e[1];
	      BtorNode * other;

	      if (btor_node_is_bv_const (left))
		other = right;
	      else if (btor_node_is_bv_const (right))
		other = left;
	      else
		other = 0;

	      // FIXME fails with symbolic lemmas (during beta-reduction
	      // rewrite level is forced to 1, hence symbolic lemmas might
	      // not be simplified as much as possible). possible solution:
	      // use rewrite level > 1 for lemma generation.
	      //if (other 
	      //    && !btor_node_is_inverted (other) 
	      //    && btor_node_is_bv_add (other))
	      //  {
	      //    assert (!btor_node_is_bv_const (other->e[0]));
	      //    assert (!btor_node_is_bv_const (other->e[1]));
	      //  }
	    }
	}
#endif
#endif

    if (!btor_hashptr_table_get (sc, cur))
    {
      aig = exp_to_aig (btor, cur);
      if (aig == BTOR_AIG_FALSE)
      {
        btor->found_constraint_false = true;
        break;
      }
      btor_aig_add_toplevel_to_sat (amgr, aig);
      btor_aig_release (amgr, aig);
      (void) btor_hashptr_table_add (sc, cur);
      btor_hashptr_table_remove (uc, cur, 0, 0);

      btor->stats.constraints.synthesized++;
      report_constraint_stats (btor, false);
    }
    else
    {
      /* constraint is already in sc */
      btor_hashptr_table_remove (uc, cur, 0, 0);
      btor_node_release (btor, cur);
    }
  }
}

void
btor_insert_unsynthesized_constraint (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!btor_node_real_addr (exp)->parameterized);

  BtorBitVector *bits;
  BtorPtrHashTable *uc;

  if (btor_node_is_bv_const (exp))
  {
    bits = btor_node_bv_const_get_bits (exp);
    assert (btor_bv_get_width (bits) == 1);
    if ((btor_node_is_inverted (exp) && btor_bv_get_bit (bits, 0))
        || (!btor_node_is_inverted (exp) && !btor_bv_get_bit (bits, 0)))
    {
      btor->inconsistent = true;
      return;
    }
    /* we do not add true */
    assert ((btor_node_is_inverted (exp) && !btor_bv_get_bit (bits, 0))
            || (!btor_node_is_inverted (exp) && btor_bv_get_bit (bits, 0)));
    return;
  }

  uc = btor->unsynthesized_constraints;
  if (!btor_hashptr_table_get (uc, exp))
  {
    (void) btor_hashptr_table_add (uc, btor_node_copy (btor, exp));
    btor_node_real_addr (exp)->constraint = 1;
    btor->stats.constraints.unsynthesized++;
    BTORLOG (
        1, "add unsynthesized constraint: %s", btor_util_node2string (exp));
  }

  /* Insert into embedded constraint table if constraint has parents.
   * Expressions containing embedded constraints get rebuilt and the embedded
   * constraint is substituted by true/false. */
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1
      && btor_node_real_addr (exp)->parents > 0
      && !btor_hashptr_table_get (btor->embedded_constraints, exp))
  {
    assert (!btor_node_is_bv_const (exp));
    (void) btor_hashptr_table_add (btor->embedded_constraints,
                                   btor_node_copy (btor, exp));
    btor->stats.constraints.embedded++;
    BTORLOG (1,
             "add embedded constraint: %s (%u parents)",
             btor_util_node2string (exp),
             btor_node_real_addr (exp)->parents);
  }
}

static bool
constraint_is_inconsistent (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  //  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1);
  assert (btor_node_bv_get_width (btor, exp) == 1);

  exp = btor_simplify_exp (btor, exp);

  return btor_node_is_bv_const_zero (btor, exp)
         || btor_hashptr_table_get (btor->synthesized_constraints,
                                    btor_node_invert (exp))
         || btor_hashptr_table_get (btor->unsynthesized_constraints,
                                    btor_node_invert (exp));
}

static void
insert_into_constraint_tables (Btor *btor, BtorNode *exp)
{
  if (constraint_is_inconsistent (btor, exp))
  {
    btor->inconsistent = true;
  }
  else
  {
    if (!btor_node_real_addr (exp)->constraint)
    {
      btor_insert_unsynthesized_constraint (btor, exp);
    }
    else
    {
      assert (btor_hashptr_table_get (btor->unsynthesized_constraints, exp)
              || btor_hashptr_table_get (btor->synthesized_constraints, exp));
    }
  }
}

static void
insert_varsubst_constraint (Btor *btor, BtorNode *left, BtorNode *right)
{
  assert (btor);
  assert (left);
  assert (right);

  BtorNode *eq;
  BtorPtrHashTable *vsc;
  BtorPtrHashBucket *bucket;

  vsc    = btor->varsubst_constraints;
  bucket = btor_hashptr_table_get (vsc, left);

  if (!bucket)
  {
    BTORLOG (1,
             "add variable substitution: %s -> %s",
             btor_util_node2string (left),
             btor_util_node2string (right));

    btor_hashptr_table_add (vsc, btor_node_copy (btor, left))->data.as_ptr =
        btor_node_copy (btor, right);

    btor->stats.constraints.varsubst++;

    /* Always add varsubst contraints into unsynthesized/embedded contraints.
     * Otherwise, we get an inconsistent state if varsubst is disabled and
     * not all varsubst constraints have been processed. */
    eq = btor_exp_eq (btor, left, right);
    insert_into_constraint_tables (btor, eq);
    btor_node_release (btor, eq);
  }
  /* if v = t_1 is already in varsubst, we have to synthesize v = t_2 */
  else if (right != (BtorNode *) bucket->data.as_ptr)
  {
    eq = btor_exp_eq (btor, left, right);
    insert_into_constraint_tables (btor, eq);
    btor_node_release (btor, eq);
  }
}

static BtorSubstCompKind
reverse_subst_comp_kind (Btor *btor, BtorSubstCompKind comp)
{
  assert (btor);
  (void) btor;
  switch (comp)
  {
    case BTOR_SUBST_COMP_ULT_KIND: return BTOR_SUBST_COMP_UGT_KIND;
    case BTOR_SUBST_COMP_ULTE_KIND: return BTOR_SUBST_COMP_UGTE_KIND;
    case BTOR_SUBST_COMP_UGT_KIND: return BTOR_SUBST_COMP_ULT_KIND;
    default:
      assert (comp == BTOR_SUBST_COMP_UGTE_KIND);
      return BTOR_SUBST_COMP_ULTE_KIND;
  }
}

/* check if left does not occur on the right side */
static bool
occurrence_check (Btor *btor, BtorNode *left, BtorNode *right)
{
  assert (btor);
  assert (left);
  assert (right);

  BtorNode *cur, *real_left;
  BtorNodePtrQueue queue;
  bool is_cyclic;
  uint32_t i;
  BtorMemMgr *mm;
  BtorIntHashTable *cache;

  double start = btor_util_time_stamp ();
  is_cyclic    = false;
  mm           = btor->mm;
  cache        = btor_hashint_table_new (mm);
  real_left    = btor_node_real_addr (left);
  BTOR_INIT_QUEUE (mm, queue);

  cur = btor_node_real_addr (right);
  goto OCCURRENCE_CHECK_ENTER_WITHOUT_POP;

  do
  {
    cur = btor_node_real_addr (BTOR_DEQUEUE (queue));
  OCCURRENCE_CHECK_ENTER_WITHOUT_POP:
    assert (!btor_node_is_simplified (cur)
            || btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST));
    cur = btor_node_real_addr (btor_node_get_simplified (btor, cur));

    if (real_left->id > cur->id) continue;

    if (!btor_hashint_table_contains (cache, cur->id))
    {
      btor_hashint_table_add (cache, cur->id);
      if (cur == real_left)
      {
        is_cyclic = true;
        break;
      }
      for (i = 1; i <= cur->arity; i++)
        BTOR_ENQUEUE (queue, cur->e[cur->arity - i]);
    }
  } while (!BTOR_EMPTY_QUEUE (queue));
  BTOR_RELEASE_QUEUE (queue);
  btor_hashint_table_delete (cache);
  btor->time.occurrence += btor_util_time_stamp () - start;
  return is_cyclic;
}

/* checks if we can substitute and normalizes arguments to substitution,
 * substitute left_result with right_result, exp is child of AND_NODE */
static bool
normalize_substitution (Btor *btor,
                        BtorNode *exp,
                        BtorNode **left_result,
                        BtorNode **right_result)
{
  assert (btor_opt_get (btor, BTOR_OPT_VAR_SUBST));

  BtorNode *left, *right, *real_left, *real_right, *tmp, *inv, *var, *lambda;
  BtorNode *const_exp, *e0, *e1;
  uint32_t leadings;
  BtorBitVector *ic, *fc, *bits;
  BtorMemMgr *mm;
  BtorSubstCompKind comp;
  BtorSortId sort;

  assert (btor);
  assert (exp);
  assert (left_result);
  assert (right_result);
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1);
  assert (btor_simplify_exp (btor, exp) == exp);

  mm = btor->mm;

  /* boolean BV_NODE, force assignment (right_result) w.r.t. phase */
  if (btor_node_is_bv_var (exp))
  {
    assert (btor_node_bv_get_width (btor, exp) == 1);
    sort = btor_sort_bv (btor, 1);
    if (btor_node_is_inverted (exp))
    {
      *left_result  = btor_node_copy (btor, btor_node_real_addr (exp));
      *right_result = btor_exp_bv_zero (btor, sort);
    }
    else
    {
      *left_result  = btor_node_copy (btor, exp);
      *right_result = btor_exp_bv_one (btor, sort);
    }
    btor_sort_release (btor, sort);
    return true;
  }

  if (btor_node_is_bv_ult (exp))
  {
    e0 = btor_node_get_simplified (btor, btor_node_real_addr (exp)->e[0]);
    e1 = btor_node_get_simplified (btor, btor_node_real_addr (exp)->e[1]);

    if (btor_node_is_bv_var (e0) || btor_node_is_bv_var (e1))
    {
      if (btor_node_is_inverted (exp))
        comp = BTOR_SUBST_COMP_UGTE_KIND;
      else
        comp = BTOR_SUBST_COMP_ULT_KIND;

      if (btor_node_is_bv_var (e0))
      {
        var   = e0;
        right = e1;
      }
      else
      {
        assert (btor_node_is_bv_var (e1));
        var   = e1;
        right = e0;
        comp  = reverse_subst_comp_kind (btor, comp);
      }

      /* ~a comp b is equal to a reverse_comp ~b,
       * where comp in ult, ulte, ugt, ugte
       * (e.g. reverse_comp of ult is ugt) */
      if (btor_node_is_inverted (var))
      {
        var   = btor_node_real_addr (var);
        right = btor_node_invert (right);
        comp  = reverse_subst_comp_kind (btor, comp);
      }

      /* we do not create a lambda (index) if variable is already in
       * substitution table */
      assert (!btor_node_is_inverted (var));
      if (btor_hashptr_table_get (btor->varsubst_constraints, var))
        return false;

      if (!btor_node_is_bv_const (right)) return false;

      if (btor_node_is_inverted (right))
        bits = btor_bv_not (mm, btor_node_bv_const_get_bits (right));
      else
        bits = btor_bv_copy (mm, btor_node_bv_const_get_bits (right));

      if (comp == BTOR_SUBST_COMP_ULT_KIND || comp == BTOR_SUBST_COMP_ULTE_KIND)
      {
        leadings = btor_bv_get_num_leading_zeros (bits);
        if (leadings > 0)
        {
          sort      = btor_sort_bv (btor, leadings);
          const_exp = btor_exp_bv_zero (btor, sort);
          btor_sort_release (btor, sort);
          sort   = btor_sort_bv (btor,
                               btor_node_bv_get_width (btor, var) - leadings);
          lambda = btor_exp_var (btor, sort, 0);
          btor_sort_release (btor, sort);
          tmp = btor_exp_bv_concat (btor, const_exp, lambda);
          insert_varsubst_constraint (btor, var, tmp);
          btor_node_release (btor, const_exp);
          btor_node_release (btor, lambda);
          btor_node_release (btor, tmp);
        }
      }
      else
      {
        assert (comp == BTOR_SUBST_COMP_UGT_KIND
                || comp == BTOR_SUBST_COMP_UGTE_KIND);
        leadings = btor_bv_get_num_leading_ones (bits);
        if (leadings > 0)
        {
          sort      = btor_sort_bv (btor, leadings);
          const_exp = btor_exp_bv_ones (btor, sort);
          btor_sort_release (btor, sort);
          sort   = btor_sort_bv (btor,
                               btor_node_bv_get_width (btor, var) - leadings);
          lambda = btor_exp_var (btor, sort, 0);
          btor_sort_release (btor, sort);
          tmp = btor_exp_bv_concat (btor, const_exp, lambda);
          insert_varsubst_constraint (btor, var, tmp);
          btor_node_release (btor, const_exp);
          btor_node_release (btor, lambda);
          btor_node_release (btor, tmp);
        }
      }

      btor_bv_free (btor->mm, bits);
      return false;
    }
  }

  /* in the boolean case a != b is the same as a == ~b */
  if (btor_node_is_inverted (exp) && btor_node_is_bv_eq (exp)
      && btor_node_bv_get_width (btor, btor_node_real_addr (exp)->e[0]) == 1)
  {
    left  = btor_node_get_simplified (btor, btor_node_real_addr (exp)->e[0]);
    right = btor_node_get_simplified (btor, btor_node_real_addr (exp)->e[1]);

    if (btor_node_is_bv_var (left))
    {
      *left_result  = btor_node_copy (btor, left);
      *right_result = btor_node_invert (btor_node_copy (btor, right));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }

    if (btor_node_is_bv_var (right))
    {
      *left_result  = btor_node_copy (btor, right);
      *right_result = btor_node_invert (btor_node_copy (btor, left));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }
  }

  if (btor_node_is_inverted (exp) || !btor_node_is_array_or_bv_eq (exp))
    return false;

  left       = btor_node_get_simplified (btor, exp->e[0]);
  right      = btor_node_get_simplified (btor, exp->e[1]);
  real_left  = btor_node_real_addr (left);
  real_right = btor_node_real_addr (right);

  if (!btor_node_is_bv_var (real_left) && !btor_node_is_bv_var (real_right)
      && !btor_node_is_uf (real_left) && !btor_node_is_uf (real_right))
  {
    if (btor_rewrite_linear_term (btor, left, &fc, left_result, &tmp))
      *right_result = btor_exp_bv_sub (btor, right, tmp);
    else if (btor_rewrite_linear_term (btor, right, &fc, left_result, &tmp))
      *right_result = btor_exp_bv_sub (btor, left, tmp);
    else
      return false;

    btor->stats.gaussian_eliminations++;

    btor_node_release (btor, tmp);
    ic = btor_bv_mod_inverse (btor->mm, fc);
    btor_bv_free (btor->mm, fc);
    inv = btor_exp_bv_const (btor, ic);
    btor_bv_free (btor->mm, ic);
    tmp = btor_exp_bv_mul (btor, *right_result, inv);
    btor_node_release (btor, inv);
    btor_node_release (btor, *right_result);
    *right_result = tmp;
  }
  else
  {
    if ((!btor_node_is_bv_var (real_left) && btor_node_is_bv_var (real_right))
        || (!btor_node_is_uf (real_left) && btor_node_is_uf (real_right)))
    {
      *left_result  = right;
      *right_result = left;
    }
    else
    {
      *left_result  = left;
      *right_result = right;
    }

    btor_node_copy (btor, left);
    btor_node_copy (btor, right);
  }

BTOR_NORMALIZE_SUBST_RESULT:
  if (btor_node_is_inverted (*left_result))
  {
    *left_result  = btor_node_invert (*left_result);
    *right_result = btor_node_invert (*right_result);
  }

  if (occurrence_check (btor, *left_result, *right_result))
  {
    btor_node_release (btor, *left_result);
    btor_node_release (btor, *right_result);
    return false;
  }

  return true;
}

static void
insert_new_constraint (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_bv_get_width (btor, exp) == 1);
  assert (!btor_node_real_addr (exp)->parameterized);

  BtorBitVector *bits;
  BtorNode *left, *right, *real_exp;

  exp      = btor_simplify_exp (btor, exp);
  real_exp = btor_node_real_addr (exp);

  if (btor_node_is_bv_const (real_exp))
  {
    bits = btor_node_bv_const_get_bits (real_exp);
    assert (btor_bv_get_width (bits) == 1);
    /* we do not add true/false */
    if ((btor_node_is_inverted (exp) && btor_bv_get_bit (bits, 0))
        || (!btor_node_is_inverted (exp) && !btor_bv_get_bit (bits, 0)))
    {
      BTORLOG (1,
               "inserted inconsistent constraint %s",
               btor_util_node2string (exp));
      btor->inconsistent = true;
    }
    else
    {
      assert ((btor_node_is_inverted (exp) && !btor_bv_get_bit (bits, 0))
              || (!btor_node_is_inverted (exp) && btor_bv_get_bit (bits, 0)));
    }
    return;
  }

  if (!btor_hashptr_table_get (btor->synthesized_constraints, exp))
  {
    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1
        && btor_opt_get (btor, BTOR_OPT_VAR_SUBST)
        && normalize_substitution (btor, exp, &left, &right))
    {
      insert_varsubst_constraint (btor, left, right);
      btor_node_release (btor, left);
      btor_node_release (btor, right);
    }
    else
    {
      insert_into_constraint_tables (btor, exp);
      report_constraint_stats (btor, false);
    }
  }
}

void
btor_reset_assumptions (Btor *btor)
{
  assert (btor);

  BtorPtrHashTableIterator it;
  uint32_t i;

  BTORLOG (2, "reset assumptions");

  btor_iter_hashptr_init (&it, btor->assumptions);
  btor_iter_hashptr_queue (&it, btor->orig_assumptions);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (btor, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (btor->assumptions);
  btor_hashptr_table_delete (btor->orig_assumptions);
  btor->assumptions =
      btor_hashptr_table_new (btor->mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->orig_assumptions =
      btor_hashptr_table_new (btor->mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);

  for (i = 0; i < BTOR_COUNT_STACK (btor->failed_assumptions); i++)
  {
    if (BTOR_PEEK_STACK (btor->failed_assumptions, i))
      btor_node_release (btor, BTOR_PEEK_STACK (btor->failed_assumptions, i));
  }
  BTOR_RESET_STACK (btor->failed_assumptions);
}

static void
reset_functions_with_model (Btor *btor)
{
  BtorNode *cur;
  uint32_t i;

  assert (btor);

  for (i = 0; i < BTOR_COUNT_STACK (btor->functions_with_model); i++)
  {
    cur = btor->functions_with_model.start[i];
    assert (!btor_node_is_inverted (cur));
    if (!btor_node_is_simplified (cur))
    {
      assert (btor_node_is_fun (cur));
      assert (cur->rho);
      btor_hashptr_table_delete (cur->rho);
      cur->rho = 0;
    }
    btor_node_release (btor, cur);
  }
  BTOR_RESET_STACK (btor->functions_with_model);
}

void
btor_reset_incremental_usage (Btor *btor)
{
  assert (btor);

  btor_reset_assumptions (btor);
  reset_functions_with_model (btor);
  btor->valid_assignments = 0;
  btor_model_delete (btor);
}

static void
add_constraint (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *cur, *child;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorIntHashTable *mark;

  exp = btor_simplify_exp (btor, exp);
  assert (!btor_node_is_fun (exp));
  assert (btor_node_bv_get_width (btor, exp) == 1);
  assert (!btor_node_real_addr (exp)->parameterized);
  mm   = btor->mm;
  mark = btor_hashint_table_new (mm);

  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!btor_node_is_inverted (exp) && btor_node_is_bv_and (exp))
  {
    BTOR_INIT_STACK (mm, stack);
    cur = exp;
    goto ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP:
      assert (!btor_node_is_inverted (cur));
      assert (btor_node_is_bv_and (cur));
      if (!btor_hashint_table_contains (mark, cur->id))
      {
        btor_hashint_table_add (mark, cur->id);
        child = cur->e[1];
        if (!btor_node_is_inverted (child) && btor_node_is_bv_and (child))
          BTOR_PUSH_STACK (stack, child);
        else
          insert_new_constraint (btor, child);
        child = cur->e[0];
        if (!btor_node_is_inverted (child) && btor_node_is_bv_and (child))
          BTOR_PUSH_STACK (stack, child);
        else
          insert_new_constraint (btor, child);
      }
    } while (!BTOR_EMPTY_STACK (stack));
    BTOR_RELEASE_STACK (stack);
  }
  else
    insert_new_constraint (btor, exp);

  btor_hashint_table_delete (mark);
  assert (btor_dbg_check_constraints_not_const (btor));
}

void
btor_assert_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!btor_node_is_fun (exp));
  assert (btor_node_bv_get_width (btor, exp) == 1);
  assert (!btor_node_real_addr (exp)->parameterized);

  add_constraint (btor, exp);
}

static int32_t
exp_to_cnf_lit (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_bv_get_width (btor, exp) == 1);

  int32_t res, sign, val;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorAIG *aig;

  exp = btor_simplify_exp (btor, exp);

  sign = 1;

  if (btor_node_is_inverted (exp))
  {
    exp = btor_node_invert (exp);
    sign *= -1;
  }

  aig = exp_to_aig (btor, exp);

  amgr = btor_get_aig_mgr (btor);
  smgr = btor_get_sat_mgr (btor);

  if (btor_aig_is_const (aig))
  {
    res = smgr->true_lit;
    if (aig == BTOR_AIG_FALSE) sign *= -1;
  }
  else
  {
    if (BTOR_IS_INVERTED_AIG (aig))
    {
      aig = BTOR_INVERT_AIG (aig);
      sign *= -1;
    }

    if (!aig->cnf_id) btor_aig_to_sat_tseitin (amgr, aig);

    res = aig->cnf_id;
    btor_aig_release (amgr, aig);

    if ((val = btor_sat_fixed (smgr, res)))
    {
      res = smgr->true_lit;
      if (val < 0) sign *= -1;
    }
  }
  res *= sign;

  return res;
}

void
btor_assume_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
  assert (exp);
  assert (!btor_node_real_addr (exp)->parameterized);

  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  BTORLOG (2,
           "assume: %s (%s)",
           btor_util_node2string (exp),
           btor_util_node2string (btor_simplify_exp (btor, exp)));

  if (!btor_hashptr_table_get (btor->orig_assumptions, exp))
  {
    btor_hashptr_table_add (btor->orig_assumptions, btor_node_copy (btor, exp));
  }

  exp = btor_simplify_exp (btor, exp);
  if (!btor_hashptr_table_get (btor->assumptions, exp))
  {
    (void) btor_hashptr_table_add (btor->assumptions,
                                   btor_node_copy (btor, exp));
  }
}

bool
btor_is_assumption_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
  assert (exp);

  BTORLOG (2, "is_assumption: %s", btor_util_node2string (exp));
  return btor_hashptr_table_get (btor->orig_assumptions, exp) ? true : false;
}

bool
btor_failed_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
  assert (btor->last_sat_result == BTOR_RESULT_UNSAT);
  assert (exp);
  assert (btor_is_assumption_exp (btor, exp));
  BTORLOG (2,
           "check failed assumption: %s (%s)",
           btor_util_node2string (exp),
           btor_util_node2string (btor_simplify_exp (btor, exp)));

  bool res;
  int32_t i, lit;
  double start;
  BtorAIG *aig;
  BtorNode *real_exp, *cur, *e;
  BtorNodePtrStack work_stack, assumptions;
  BtorSATMgr *smgr;
  BtorIntHashTable *mark;

  start = btor_util_time_stamp ();

  exp = btor_simplify_exp (btor, exp);
  assert (btor_node_real_addr (exp)->btor == btor);
  assert (!btor_node_is_fun (exp));
  assert (btor_node_bv_get_width (btor, exp) == 1);
  assert (!btor_node_real_addr (exp)->parameterized);
  mark = btor_hashint_table_new (btor->mm);
  smgr = btor_get_sat_mgr (btor);
  assert (smgr);

  if (btor->inconsistent)
  {
    res = false;
  }
  else if (exp == btor->true_exp)
  {
    res = false;
  }
  else if (exp == btor_node_invert (btor->true_exp))
  {
    res = true;
  }
  else if (!btor_sat_is_initialized (smgr))
  {
    res = true;
  }
  else if (btor_node_is_inverted (exp) || !btor_node_is_bv_and (exp))
  {
    real_exp = btor_node_real_addr (exp);
    assert (btor->found_constraint_false || btor_node_is_synth (real_exp));

    if (!btor_node_is_synth (real_exp))
    {
      res = false;
    }
    else if (btor->found_constraint_false)
    {
      res = ((btor_node_is_inverted (exp)
              && real_exp->av->aigs[0] == BTOR_AIG_TRUE)
             || (!btor_node_is_inverted (exp)
                 && real_exp->av->aigs[0] == BTOR_AIG_FALSE));
    }
    else
    {
      if ((btor_node_is_inverted (exp)
           && real_exp->av->aigs[0] == BTOR_AIG_FALSE)
          || (!btor_node_is_inverted (exp)
              && real_exp->av->aigs[0] == BTOR_AIG_TRUE))
      {
        res = false;
      }
      else
      {
        lit = exp_to_cnf_lit (btor, exp);
        if (abs (lit) == smgr->true_lit)
          res = lit < 0;
        else
          res = btor_sat_failed (smgr, lit) > 0;
      }
    }
  }
  else
  {
    res = false;
    BTOR_INIT_STACK (btor->mm, assumptions);
    BTOR_INIT_STACK (btor->mm, work_stack);
    BTOR_PUSH_STACK (work_stack, exp);
    while (!BTOR_EMPTY_STACK (work_stack))
    {
      cur = BTOR_POP_STACK (work_stack);
      assert (!btor_node_is_inverted (cur));
      assert (btor_node_is_bv_and (cur));
      if (btor_hashint_table_contains (mark, cur->id)) continue;
      btor_hashint_table_add (mark, cur->id);
      for (i = 0; i < 2; i++)
      {
        e = cur->e[i];
        if (!btor_node_is_inverted (e) && btor_node_is_bv_and (e))
          BTOR_PUSH_STACK (work_stack, e);
        else
        {
          if (!btor_node_is_synth (btor_node_real_addr (e))) continue;

          aig = btor_node_real_addr (e)->av->aigs[0];
          if ((btor_node_is_inverted (e) && aig == BTOR_AIG_FALSE)
              || (!btor_node_is_inverted (e) && aig == BTOR_AIG_TRUE))
            continue;
          if ((btor_node_is_inverted (e) && aig == BTOR_AIG_TRUE)
              || (!btor_node_is_inverted (e) && aig == BTOR_AIG_FALSE))
            goto ASSUMPTION_FAILED;
          if (btor->found_constraint_false) continue;
          BTOR_PUSH_STACK (assumptions, e);
        }
      }
    }

    while (!BTOR_EMPTY_STACK (assumptions))
    {
      cur = BTOR_POP_STACK (assumptions);
      assert (btor_node_is_inverted (cur) || !btor_node_is_bv_and (cur));
      lit = exp_to_cnf_lit (btor, cur);
      if (lit == smgr->true_lit) continue;
      if (lit == -smgr->true_lit || btor_sat_failed (smgr, lit))
      {
      ASSUMPTION_FAILED:
        res = true;
        break;
      }
    }
    BTOR_RELEASE_STACK (work_stack);
    BTOR_RELEASE_STACK (assumptions);
  }

  btor_hashint_table_delete (mark);
  btor->time.failed += btor_util_time_stamp () - start;

  return res;
}

void
btor_fixate_assumptions (Btor *btor)
{
  BtorNode *exp;
  BtorNodePtrStack stack;
  BtorPtrHashTableIterator it;
  size_t i;

  BTOR_INIT_STACK (btor->mm, stack);
  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    BTOR_PUSH_STACK (stack,
                     btor_node_copy (btor, btor_iter_hashptr_next (&it)));
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    exp = BTOR_PEEK_STACK (stack, i);
    btor_assert_exp (btor, exp);
    btor_node_release (btor, exp);
  }
  BTOR_RELEASE_STACK (stack);
  btor_reset_assumptions (btor);
}

/*------------------------------------------------------------------------*/

static void
replace_constraint (Btor *btor, BtorNode *old, BtorNode *new)
{
  assert (btor);
  assert (old);
  assert (btor_node_is_regular (old));
  assert (old->constraint);
  assert (old->refs > 1);
  assert (!old->parameterized);
  assert (!btor_node_real_addr (new)->parameterized);
  assert (btor_node_is_simplified (old));
  assert (!btor_node_is_simplified (new));

  BtorPtrHashTable *unsynthesized_constraints, *synthesized_constraints;
  BtorPtrHashTable *embedded_constraints, *pos, *neg;
  BtorNode *not_new, *not_old;

  BTORLOG (1,
           "replace constraint: %s -> %s",
           btor_util_node2string (old),
           btor_util_node2string (new));

  not_old                   = btor_node_invert (old);
  not_new                   = btor_node_invert (new);
  embedded_constraints      = btor->embedded_constraints;
  unsynthesized_constraints = btor->unsynthesized_constraints;
  synthesized_constraints   = btor->synthesized_constraints;
  pos = neg = 0;

  if (btor_hashptr_table_get (unsynthesized_constraints, old))
  {
    add_constraint (btor, new);
    assert (!pos);
    pos = unsynthesized_constraints;
  }

  if (btor_hashptr_table_get (unsynthesized_constraints, not_old))
  {
    add_constraint (btor, not_new);
    assert (!neg);
    neg = unsynthesized_constraints;
  }

  if (btor_hashptr_table_get (synthesized_constraints, old))
  {
    add_constraint (btor, new);
    assert (!pos);
    pos = synthesized_constraints;
  }

  if (btor_hashptr_table_get (synthesized_constraints, not_old))
  {
    add_constraint (btor, not_new);
    assert (!neg);
    neg = synthesized_constraints;
  }

  if (pos)
  {
    btor_hashptr_table_remove (pos, old, 0, 0);
    btor_node_release (btor, old);

    if (btor_hashptr_table_get (embedded_constraints, old))
    {
      btor_hashptr_table_remove (embedded_constraints, old, 0, 0);
      btor_node_release (btor, old);
    }
  }

  if (neg)
  {
    btor_hashptr_table_remove (neg, not_old, 0, 0);
    btor_node_release (btor, not_old);

    if (btor_hashptr_table_get (embedded_constraints, not_old))
    {
      btor_hashptr_table_remove (embedded_constraints, not_old, 0, 0);
      btor_node_release (btor, not_old);
    }
  }

  old->constraint = 0;
}

void
btor_set_simplified_exp (Btor *btor, BtorNode *exp, BtorNode *simplified)
{
  assert (btor);
  assert (exp);
  assert (simplified);
  assert (btor_node_is_regular (exp));
  assert (exp != btor_node_real_addr (simplified));
  assert (!btor_node_real_addr (simplified)->simplified);
  assert (exp->arity <= 3);
  assert (btor_node_get_sort_id (exp) == btor_node_get_sort_id (simplified));
  assert (exp->parameterized
          || !btor_node_real_addr (simplified)->parameterized);
  assert (!btor_node_real_addr (simplified)->parameterized
          || exp->parameterized);

  BTORLOG (2,
           "set simplified: %s -> %s (synth: %u, param: %u)",
           btor_util_node2string (exp),
           btor_util_node2string (simplified),
           btor_node_is_synth (exp),
           exp->parameterized);

  /* FIXME: indicator for slow-down in incremental mode, when too many
   * synthesized nodes are rewritten, it can significantly slow-down the
   * solver. */
  if (btor_node_is_synth (exp)) btor->stats.rewrite_synth++;

  if (exp->simplified) btor_node_release (btor, exp->simplified);

  exp->simplified = btor_node_copy (btor, simplified);

  if (exp->constraint) replace_constraint (btor, exp, exp->simplified);

  if (!btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST))
  {
    btor_node_set_to_proxy (btor, exp);

    /* if simplified is parameterized, exp was also parameterized */
    if (btor_node_real_addr (simplified)->parameterized) exp->parameterized = 1;
  }
}

/* Finds most simplified expression and shortens path to it */
static BtorNode *
recursively_pointer_chase_simplified_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp, *cur, *simplified, *not_simplified, *next;
  bool invert;

  assert (btor);
  assert (exp);

  real_exp = btor_node_real_addr (exp);

  assert (real_exp->simplified);
  assert (btor_node_real_addr (real_exp->simplified)->simplified);

  /* shorten path to simplified expression */
  invert     = false;
  simplified = real_exp->simplified;
  do
  {
    assert (!btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST)
            || !btor_node_is_proxy (simplified));
    assert (btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST)
            || btor_node_is_proxy (simplified));
    if (btor_node_is_inverted (simplified)) invert = !invert;
    simplified = btor_node_real_addr (simplified)->simplified;
  } while (btor_node_real_addr (simplified)->simplified);
  /* 'simplified' is representative element */
  assert (!btor_node_real_addr (simplified)->simplified);
  if (invert) simplified = btor_node_invert (simplified);

  invert         = false;
  not_simplified = btor_node_invert (simplified);
  cur            = btor_node_copy (btor, real_exp);
  do
  {
    if (btor_node_is_inverted (cur)) invert = !invert;
    cur  = btor_node_real_addr (cur);
    next = btor_node_copy (btor, cur->simplified);
    btor_set_simplified_exp (btor, cur, invert ? not_simplified : simplified);
    btor_node_release (btor, cur);
    cur = next;
  } while (btor_node_real_addr (cur)->simplified);
  btor_node_release (btor, cur);

  /* if starting expression is inverted, then we have to invert result */
  if (btor_node_is_inverted (exp)) simplified = btor_node_invert (simplified);

  return simplified;
}

BtorNode *
btor_node_get_simplified (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST)
          || !btor_node_is_proxy (exp));

  (void) btor;
  BtorNode *real_exp;

  real_exp = btor_node_real_addr (exp);

  /* no simplified expression ? */
  if (!real_exp->simplified)
  {
    return exp;
  }

  /* only one simplified expression ? */
  if (!btor_node_real_addr (real_exp->simplified)->simplified)
  {
    if (btor_node_is_inverted (exp))
      return btor_node_invert (real_exp->simplified);
    return exp->simplified;
  }
  return recursively_pointer_chase_simplified_exp (btor, exp);
}

static BtorNode *
simplify_constraint_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_real_addr (exp)->constraint);
  assert (!btor_node_real_addr (exp)->simplified);
  /* embedded constraints rewriting enabled with rwl > 1 */
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1);

  BtorNode *real_exp, *result, *not_exp;

  real_exp = btor_node_real_addr (exp);

  /* Do not simplify top-level constraint applies (we need the implication
   * dependencies for determining top applies when dual prop enabled) */
  if (btor_opt_get (btor, BTOR_OPT_FUN_DUAL_PROP)
      && btor_node_is_apply (real_exp))
    return exp;

  not_exp = btor_node_invert (real_exp);

  if (btor_node_is_bv_const (real_exp)) return exp;

  if (btor_hashptr_table_get (btor->unsynthesized_constraints, real_exp))
  {
    result = btor->true_exp;
  }
  else if (btor_hashptr_table_get (btor->unsynthesized_constraints, not_exp))
  {
    result = btor_node_invert (btor->true_exp);
  }
  else if (btor_hashptr_table_get (btor->synthesized_constraints, real_exp))
  {
    result = btor->true_exp;
  }
  else
  {
    assert (btor_hashptr_table_get (btor->synthesized_constraints, not_exp));
    result = btor_node_invert (btor->true_exp);
  }

  if (btor_node_is_inverted (exp)) return btor_node_invert (result);

  return result;
}

BtorNode *
btor_simplify_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_real_addr (exp)->btor == btor);
  assert (btor_node_real_addr (exp)->refs > 0);

  BtorNode *result;

  result = btor_node_get_simplified (btor, exp);

  /* NOTE: embedded constraints rewriting is enabled with rwl > 1 */
  if (btor_opt_get (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS)
      && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1
      && btor_node_real_addr (result)->constraint)
    return simplify_constraint_exp (btor, result);

  assert (btor_node_real_addr (result)->btor == btor);
  assert (btor_node_real_addr (result)->refs > 0);

  return result;
}

BtorNode *
btor_substitute_nodes_node_map (Btor *btor,
                                BtorNode *root,
                                BtorNodeMap *substs,
                                BtorIntHashTable *node_map)
{
  assert (btor);
  assert (root);
  assert (substs);

  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *subst, *result, **e;
  BtorNodePtrStack visit, args, cleanup;
  BtorIntHashTable *mark, *mark_subst;
  BtorHashTableData *d;
  BtorNodeMapIterator it;

  mm         = btor->mm;
  mark       = btor_hashint_map_new (mm);
  mark_subst = btor_hashint_map_new (mm);
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, cleanup);
  BTOR_PUSH_STACK (visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);
    d        = btor_hashint_map_get (mark, real_cur->id);
    if (!d)
    {
      subst = btor_nodemap_mapped (substs, real_cur);
      if (subst)
      {
        /* if this assertion fails we have a cyclic substitution */
        assert (!btor_hashint_map_get (mark, btor_node_real_addr (subst)->id)
                || btor_hashint_map_get (mark, btor_node_real_addr (subst)->id)
                       ->as_ptr);
        BTOR_PUSH_STACK (visit, btor_node_cond_invert (cur, subst));
        btor_hashint_table_add (mark_subst, btor_node_real_addr (subst)->id);
        continue;
      }

      (void) btor_hashint_map_add (mark, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_node_is_param (real_cur)
            /* Do not create new param if 'real_cur' is already a
             * substitution */
            && !btor_hashint_table_contains (mark_subst, real_cur->id))
        {
          // TODO: make unique symbol !<num>++
          result = btor_exp_param (btor, real_cur->sort_id, 0);
        }
        else
          result = btor_node_copy (btor, real_cur);
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      else
      {
        /* if the param of a quantifier gets subtituted by a non-param,
         * we do not create a quantifier, but return the body instead */
        if (btor_node_is_quantifier (real_cur) && !btor_node_is_param (e[0]))
          result = btor_node_copy (btor, e[1]);
        else
          result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);
      }
      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);
      BTOR_PUSH_STACK (cleanup, result);
      if (node_map)
      {
        assert (!btor_hashint_map_contains (node_map, real_cur->id));
        btor_hashint_map_add (node_map, real_cur->id)->as_int =
            btor_node_real_addr (result)->id;
      }
    PUSH_RESULT:
      assert (real_cur->sort_id == btor_node_real_addr (result)->sort_id);
      BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, result));
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  /* update 'node_map' for substituted nodes */
  if (node_map)
  {
    btor_iter_nodemap_init (&it, substs);
    while (btor_iter_nodemap_has_next (&it))
    {
      subst = it.it.bucket->data.as_ptr;
      while (btor_nodemap_mapped (substs, subst))
        subst = btor_nodemap_mapped (substs, subst);
      cur = btor_iter_nodemap_next (&it);
      assert (!btor_hashint_map_contains (node_map, cur->id));
      btor_hashint_map_add (node_map, cur->id)->as_int =
          btor_node_real_addr (subst)->id;
    }
  }

  while (!BTOR_EMPTY_STACK (cleanup))
    btor_node_release (btor, BTOR_POP_STACK (cleanup));
  BTOR_RELEASE_STACK (cleanup);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);
  btor_hashint_map_delete (mark);
  btor_hashint_map_delete (mark_subst);
  return result;
}

BtorNode *
btor_substitute_nodes (Btor *btor, BtorNode *root, BtorNodeMap *substs)
{
  return btor_substitute_nodes_node_map (btor, root, substs, 0);
}

BtorNode *
btor_substitute_node (Btor *btor,
                      BtorNode *root,
                      BtorNode *node,
                      BtorNode *subst)
{
  BtorNodeMap *map = btor_nodemap_new (btor);
  btor_nodemap_map (map, node, subst);
  BtorNode *result = btor_substitute_nodes_node_map (btor, root, map, 0);
  btor_nodemap_delete (map);
  return result;
}

/*------------------------------------------------------------------------*/

/* bit vector skeleton is always encoded, i.e., if btor_node_is_synth is true,
 * then it is also encoded. with option lazy_synthesize enabled,
 * 'btor_synthesize_exp' stops at feq and apply nodes */
void
btor_synthesize_exp (Btor *btor,
                     BtorNode *exp,
                     BtorPtrHashTable *backannotation)
{
  BtorNodePtrStack exp_stack;
  BtorNode *cur, *value, *args;
  BtorAIGVec *av0, *av1, *av2;
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *static_rho;
  BtorPtrHashTableIterator it;
  char *indexed_name;
  const char *name;
  uint32_t count, i, j, len;
  bool is_same_children_mem;
  bool invert_av0 = false;
  bool invert_av1 = false;
  bool invert_av2 = false;
  double start;
  bool restart, opt_lazy_synth;
  BtorIntHashTable *cache;

  assert (btor);
  assert (exp);

  start          = btor_util_time_stamp ();
  mm             = btor->mm;
  avmgr          = btor->avmgr;
  count          = 0;
  cache          = btor_hashint_table_new (mm);
  opt_lazy_synth = btor_opt_get (btor, BTOR_OPT_FUN_LAZY_SYNTHESIZE) == 1;

  BTOR_INIT_STACK (mm, exp_stack);
  BTOR_PUSH_STACK (exp_stack, exp);
  BTORLOG (2, "%s: %s", __FUNCTION__, btor_util_node2string (exp));

  while (!BTOR_EMPTY_STACK (exp_stack))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (exp_stack));
    assert (!btor_node_is_proxy (cur));
    assert (!btor_node_is_simplified (cur));

    if (btor_node_is_synth (cur)) continue;

    count++;
    if (!btor_hashint_table_contains (cache, cur->id))
    {
      if (btor_node_is_bv_const (cur))
      {
        cur->av = btor_aigvec_const (avmgr, btor_node_bv_const_get_bits (cur));
        BTORLOG (2, "  synthesized: %s", btor_util_node2string (cur));
        /* no need to call btor_aigvec_to_sat_tseitin here */
      }
      /* encode bv skeleton inputs: var, apply, feq */
      else if (btor_node_is_bv_var (cur)
               || (btor_node_is_apply (cur) && !cur->parameterized)
               || btor_node_is_fun_eq (cur))
      {
        assert (!cur->parameterized);
        cur->av = btor_aigvec_var (avmgr, btor_node_bv_get_width (btor, cur));

        if (btor_node_is_bv_var (cur) && backannotation
            && (name = btor_node_get_symbol (btor, cur)))
        {
          len = strlen (name) + 40;
          if (btor_node_bv_get_width (btor, cur) > 1)
          {
            indexed_name = btor_mem_malloc (mm, len);
            for (i = 0; i < cur->av->width; i++)
            {
              b = btor_hashptr_table_add (backannotation, cur->av->aigs[i]);
              assert (b->key == cur->av->aigs[i]);
              sprintf (indexed_name, "%s[%d]", name, cur->av->width - i - 1);
              b->data.as_str = btor_mem_strdup (mm, indexed_name);
            }
            btor_mem_free (mm, indexed_name, len);
          }
          else
          {
            assert (btor_node_bv_get_width (btor, cur) == 1);
            b = btor_hashptr_table_add (backannotation, cur->av->aigs[0]);
            assert (b->key == cur->av->aigs[0]);
            b->data.as_str = btor_mem_strdup (mm, name);
          }
        }
        BTORLOG (2, "  synthesized: %s", btor_util_node2string (cur));
        btor_aigvec_to_sat_tseitin (avmgr, cur->av);

        /* continue synthesizing children for apply and feq nodes if
         * lazy_synthesize is disabled */
        if (!opt_lazy_synth) goto PUSH_CHILDREN;
      }
      /* we stop at function nodes as they will be lazily synthesized and
       * encoded during consistency checking */
      else if (btor_node_is_fun (cur) && opt_lazy_synth)
      {
        continue;
      }
      else
      {
      PUSH_CHILDREN:
        assert (!opt_lazy_synth || !btor_node_is_fun (cur));

        btor_hashint_table_add (cache, cur->id);
        BTOR_PUSH_STACK (exp_stack, cur);
        for (j = 1; j <= cur->arity; j++)
          BTOR_PUSH_STACK (exp_stack, cur->e[cur->arity - j]);

        /* synthesize nodes in static_rho of lambda nodes */
        if (btor_node_is_lambda (cur))
        {
          static_rho = btor_node_lambda_get_static_rho (cur);
          if (static_rho)
          {
            btor_iter_hashptr_init (&it, static_rho);
            while (btor_iter_hashptr_has_next (&it))
            {
              value = it.bucket->data.as_ptr;
              args  = btor_iter_hashptr_next (&it);
              BTOR_PUSH_STACK (exp_stack, btor_simplify_exp (btor, value));
              BTOR_PUSH_STACK (exp_stack, btor_simplify_exp (btor, args));
            }
          }
        }
      }
    }
    /* paremterized nodes, argument nodes and functions are not
     * synthesizable */
    else if (!cur->parameterized && !btor_node_is_args (cur)
             && !btor_node_is_fun (cur))
    {
      if (!opt_lazy_synth)
      {
        /* due to pushing nodes from static_rho onto 'exp_stack' a strict
         * DFS order is not guaranteed anymore. hence, we have to check
         * if one of the children of 'cur' is not yet synthesized and
         * thus, have to synthesize them before 'cur'. */
        restart = false;
        for (i = 0; i < cur->arity; i++)
        {
          if (!btor_node_is_synth (btor_node_real_addr (cur->e[i])))
          {
            BTOR_PUSH_STACK (exp_stack, cur->e[i]);
            restart = true;
            break;
          }
        }
        if (restart) continue;
      }

      if (cur->arity == 1)
      {
        assert (btor_node_is_bv_slice (cur));
        invert_av0 = btor_node_is_inverted (cur->e[0]);
        av0        = btor_node_real_addr (cur->e[0])->av;
        if (invert_av0) btor_aigvec_invert (avmgr, av0);
        cur->av = btor_aigvec_slice (avmgr,
                                     av0,
                                     btor_node_bv_slice_get_upper (cur),
                                     btor_node_bv_slice_get_lower (cur));
        if (invert_av0) btor_aigvec_invert (avmgr, av0);
      }
      else if (cur->arity == 2)
      {
        /* We have to check if the children are in the same memory
         * place if they are in the same memory place. Then we need to
         * allocate memory for the AIG vectors if they are not, then
         * we can invert them in place and invert them back afterwards
         * (only if necessary) .
         */
        is_same_children_mem =
            btor_node_real_addr (cur->e[0]) == btor_node_real_addr (cur->e[1]);
        if (is_same_children_mem)
        {
          av0 = BTOR_AIGVEC_NODE (btor, cur->e[0]);
          av1 = BTOR_AIGVEC_NODE (btor, cur->e[1]);
        }
        else
        {
          invert_av0 = btor_node_is_inverted (cur->e[0]);
          av0        = btor_node_real_addr (cur->e[0])->av;
          if (invert_av0) btor_aigvec_invert (avmgr, av0);
          invert_av1 = btor_node_is_inverted (cur->e[1]);
          av1        = btor_node_real_addr (cur->e[1])->av;
          if (invert_av1) btor_aigvec_invert (avmgr, av1);
        }
        switch (cur->kind)
        {
          case BTOR_BV_AND_NODE:
            cur->av = btor_aigvec_and (avmgr, av0, av1);
            break;
          case BTOR_BV_EQ_NODE:
            cur->av = btor_aigvec_eq (avmgr, av0, av1);
            break;
          case BTOR_BV_ADD_NODE:
            cur->av = btor_aigvec_add (avmgr, av0, av1);
            break;
          case BTOR_BV_MUL_NODE:
            cur->av = btor_aigvec_mul (avmgr, av0, av1);
            break;
          case BTOR_BV_ULT_NODE:
            cur->av = btor_aigvec_ult (avmgr, av0, av1);
            break;
          case BTOR_BV_SLL_NODE:
            cur->av = btor_aigvec_sll (avmgr, av0, av1);
            break;
          case BTOR_BV_SRL_NODE:
            cur->av = btor_aigvec_srl (avmgr, av0, av1);
            break;
          case BTOR_BV_UDIV_NODE:
            cur->av = btor_aigvec_udiv (avmgr, av0, av1);
            break;
          case BTOR_BV_UREM_NODE:
            cur->av = btor_aigvec_urem (avmgr, av0, av1);
            break;
          default:
            assert (cur->kind == BTOR_BV_CONCAT_NODE);
            cur->av = btor_aigvec_concat (avmgr, av0, av1);
            break;
        }

        if (is_same_children_mem)
        {
          btor_aigvec_release_delete (avmgr, av0);
          btor_aigvec_release_delete (avmgr, av1);
        }
        else
        {
          if (invert_av0) btor_aigvec_invert (avmgr, av0);
          if (invert_av1) btor_aigvec_invert (avmgr, av1);
        }
        if (!opt_lazy_synth) btor_aigvec_to_sat_tseitin (avmgr, cur->av);
      }
      else
      {
        assert (cur->arity == 3);

        if (btor_node_is_bv_cond (cur))
        {
          is_same_children_mem =
              btor_node_real_addr (cur->e[0]) == btor_node_real_addr (cur->e[1])
              || btor_node_real_addr (cur->e[0])
                     == btor_node_real_addr (cur->e[2])
              || btor_node_real_addr (cur->e[1])
                     == btor_node_real_addr (cur->e[2]);
          if (is_same_children_mem)
          {
            av0 = BTOR_AIGVEC_NODE (btor, cur->e[0]);
            av1 = BTOR_AIGVEC_NODE (btor, cur->e[1]);
            av2 = BTOR_AIGVEC_NODE (btor, cur->e[2]);
          }
          else
          {
            invert_av0 = btor_node_is_inverted (cur->e[0]);
            av0        = btor_node_real_addr (cur->e[0])->av;
            if (invert_av0) btor_aigvec_invert (avmgr, av0);
            invert_av1 = btor_node_is_inverted (cur->e[1]);
            av1        = btor_node_real_addr (cur->e[1])->av;
            if (invert_av1) btor_aigvec_invert (avmgr, av1);
            invert_av2 = btor_node_is_inverted (cur->e[2]);
            av2        = btor_node_real_addr (cur->e[2])->av;
            if (invert_av2) btor_aigvec_invert (avmgr, av2);
          }
          cur->av = btor_aigvec_cond (avmgr, av0, av1, av2);
          if (is_same_children_mem)
          {
            btor_aigvec_release_delete (avmgr, av2);
            btor_aigvec_release_delete (avmgr, av1);
            btor_aigvec_release_delete (avmgr, av0);
          }
          else
          {
            if (invert_av0) btor_aigvec_invert (avmgr, av0);
            if (invert_av1) btor_aigvec_invert (avmgr, av1);
            if (invert_av2) btor_aigvec_invert (avmgr, av2);
          }
        }
      }
      assert (cur->av);
      BTORLOG (2, "  synthesized: %s", btor_util_node2string (cur));
      btor_aigvec_to_sat_tseitin (avmgr, cur->av);
    }
  }
  BTOR_RELEASE_STACK (exp_stack);
  btor_hashint_table_delete (cache);

  if (count > 0 && btor_opt_get (btor, BTOR_OPT_VERBOSITY) > 3)
    BTOR_MSG (
        btor->msg, 3, "synthesized %u expressions into AIG vectors", count);

  btor->time.synth_exp += btor_util_time_stamp () - start;
}

/* forward assumptions to the SAT solver */
void
btor_add_again_assumptions (Btor *btor)
{
  assert (btor);
  assert (btor_dbg_check_assumptions_simp_free (btor));

  int32_t i;
  BtorNode *exp, *cur, *e;
  BtorNodePtrStack stack;
  BtorPtrHashTable *assumptions;
  BtorPtrHashTableIterator it;
  BtorAIG *aig;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorIntHashTable *mark;

  amgr = btor_get_aig_mgr (btor);
  smgr = btor_get_sat_mgr (btor);

  BTOR_INIT_STACK (btor->mm, stack);
  mark = btor_hashint_table_new (btor->mm);

  assumptions = btor_hashptr_table_new (btor->mm,
                                        (BtorHashPtr) btor_node_hash_by_id,
                                        (BtorCmpPtr) btor_node_compare_by_id);

  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    exp = btor_iter_hashptr_next (&it);
    assert (!btor_node_is_simplified (exp));

    if (btor_node_is_inverted (exp) || !btor_node_is_bv_and (exp))
    {
      if (!btor_hashptr_table_get (assumptions, exp))
        btor_hashptr_table_add (assumptions, exp);
    }
    else
    {
      BTOR_PUSH_STACK (stack, exp);
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_POP_STACK (stack);
        assert (!btor_node_is_inverted (cur));
        assert (btor_node_is_bv_and (cur));
        if (btor_hashint_table_contains (mark, cur->id)) continue;
        btor_hashint_table_add (mark, cur->id);
        for (i = 0; i < 2; i++)
        {
          e = cur->e[i];
          if (!btor_node_is_inverted (e) && btor_node_is_bv_and (e))
            BTOR_PUSH_STACK (stack, e);
          else if (!btor_hashptr_table_get (assumptions, e))
            btor_hashptr_table_add (assumptions, e);
        }
      }
    }
  }

  btor_iter_hashptr_init (&it, assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (btor_node_bv_get_width (btor, cur) == 1);
    assert (!btor_node_is_simplified (cur));
    aig = exp_to_aig (btor, cur);
    btor_aig_to_sat (amgr, aig);
    if (aig == BTOR_AIG_TRUE) continue;
    if (btor_sat_is_initialized (smgr))
    {
      assert (btor_aig_get_cnf_id (aig) != 0);
      btor_sat_assume (smgr, btor_aig_get_cnf_id (aig));
    }
    btor_aig_release (amgr, aig);
  }

  BTOR_RELEASE_STACK (stack);
  btor_hashptr_table_delete (assumptions);
  btor_hashint_table_delete (mark);
}

#if 0
/* updates SAT assignments, reads assumptions and
 * returns if an assignment has changed
 */
static int32_t
update_sat_assignments (Btor * btor)
{
  assert (btor);

  BtorSATMgr *smgr;

  smgr = btor_get_sat_mgr (btor);
  add_again_assumptions (btor);
#ifndef NDEBUG
  int32_t result;
  result = timed_sat_sat (btor, -1);
  assert (result == BTOR_SAT);
#else
  (void) timed_sat_sat (btor, -1);
#endif
  return btor_sat_changed (smgr);
}
#endif

int32_t
btor_check_sat (Btor *btor, int32_t lod_limit, int32_t sat_limit)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
          || btor->btor_sat_btor_called == 0);

#ifndef NDEBUG
  bool check = true;
#endif
  double start, delta;
  BtorSolverResult res;
  uint32_t engine;

  start = btor_util_time_stamp ();

  BTOR_MSG (btor->msg, 1, "calling SAT");

  if (btor->valid_assignments == 1) btor_reset_incremental_usage (btor);

  /* 'btor->assertions' contains all assertions that were asserted in context
   * levels > 0 (boolector_push). We assume all these assertions on every
   * btor_check_sat call since these assumptions are valid until the
   * corresponding context is popped. */
  if (BTOR_COUNT_STACK (btor->assertions) > 0)
  {
    assert (BTOR_COUNT_STACK (btor->assertions_trail) > 0);
    uint32_t i;
    for (i = 0; i < BTOR_COUNT_STACK (btor->assertions); i++)
    {
      btor_assume_exp (btor, BTOR_PEEK_STACK (btor->assertions, i));
    }
  }

#ifndef NDEBUG
  // NOTE: disable checking if quantifiers present for now (not supported yet)
  if (btor->quantifiers->count) check = false;

  Btor *uclone = 0;
  if (check && btor_opt_get (btor, BTOR_OPT_CHK_UNCONSTRAINED)
      && btor_opt_get (btor, BTOR_OPT_UCOPT)
      && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
      && !btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
      && !btor_opt_get (btor, BTOR_OPT_MODEL_GEN)
      && !btor_opt_get (btor, BTOR_OPT_PRINT_DIMACS))
  {
    uclone = btor_clone_btor (btor);
    btor_opt_set (uclone, BTOR_OPT_UCOPT, 0);
    btor_opt_set (uclone, BTOR_OPT_CHK_UNCONSTRAINED, 0);
    btor_opt_set (uclone, BTOR_OPT_CHK_MODEL, 0);
    btor_opt_set (uclone, BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0);
    btor_set_term (uclone, 0, 0);

    btor_opt_set (uclone, BTOR_OPT_ENGINE, BTOR_ENGINE_FUN);
    if (uclone->slv)
    {
      uclone->slv->api.delet (uclone->slv);
      uclone->slv = 0;
    }
  }
  BtorCheckModelContext *chkmodel = 0;
  if (check && btor_opt_get (btor, BTOR_OPT_CHK_MODEL))
  {
    chkmodel = btor_check_model_init (btor);
  }
#endif

#ifndef NBTORLOG
  btor_opt_log_opts (btor);
#endif

  /* set option based on formula characteristics */

  /* eliminate lambdas (define-fun) in the QF_BV case */
  if (btor->ufs->count == 0 && btor->feqs->count == 0
      && btor->lambdas->count > 0)
  {
    BTOR_MSG(btor->msg, 1,
             "no UFs or function equalities, enable beta-reduction=all");
    btor_opt_set (btor, BTOR_OPT_BETA_REDUCE, BTOR_BETA_REDUCE_ALL);
  }

  // FIXME (ma): not sound with slice elimination. see red-vsl.proof3106.smt2
  /* disabling slice elimination is better on QF_ABV and BV */
  if (btor->ufs->count > 0 || btor->quantifiers->count > 0)
  {
    BTOR_MSG(btor->msg, 1,
             "found %s, disable slice elimination",
             btor->ufs->count > 0 ? "UFs" : "quantifiers");
    btor_opt_set (btor, BTOR_OPT_ELIMINATE_SLICES, 0);
  }

  /* set options for quantifiers */
  if (btor->quantifiers->count > 0)
  {
    btor_opt_set (btor, BTOR_OPT_UCOPT, 0);
    btor_opt_set (btor, BTOR_OPT_BETA_REDUCE, BTOR_BETA_REDUCE_ALL);
  }

  res = btor_simplify (btor);

  if (res != BTOR_RESULT_UNSAT)
  {
    engine = btor_opt_get (btor, BTOR_OPT_ENGINE);

    if (!btor->slv)
    {
      /* these engines work on QF_BV only */
      if (engine == BTOR_ENGINE_SLS && btor->ufs->count == 0
          && btor->feqs->count == 0)
      {
        assert (btor->lambdas->count == 0
                || btor_opt_get (btor, BTOR_OPT_BETA_REDUCE));
        BTOR_ABORT(btor->quantifiers->count,
                   "Quantifiers not supported for -E sls");
        btor->slv = btor_new_sls_solver (btor);
      }
      else if (engine == BTOR_ENGINE_PROP && btor->ufs->count == 0
               && btor->feqs->count == 0)
      {
        assert (btor->lambdas->count == 0
                || btor_opt_get (btor, BTOR_OPT_BETA_REDUCE));
        BTOR_ABORT(btor->quantifiers->count,
                   "Quantifiers not supported for -E prop");
        btor->slv = btor_new_prop_solver (btor);
      }
      else if (engine == BTOR_ENGINE_AIGPROP && btor->ufs->count == 0
               && btor->feqs->count == 0)
      {
        assert (btor->lambdas->count == 0
                || btor_opt_get (btor, BTOR_OPT_BETA_REDUCE));
        BTOR_ABORT(btor->quantifiers->count,
                   "Quantifiers not supported for -E aigprop");
        btor->slv = btor_new_aigprop_solver (btor);
      }
      else if ((engine == BTOR_ENGINE_QUANT && btor->quantifiers->count > 0)
               || btor->quantifiers->count > 0)
      {
        BtorPtrHashTableIterator it;
        BtorNode *cur;
        btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
        btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
        while (btor_iter_hashptr_has_next (&it))
        {
          cur = btor_iter_hashptr_next (&it);
          BTOR_ABORT (cur->lambda_below || cur->apply_below,
                      "quantifiers with functions not supported yet");
        }
        btor->slv = btor_new_quantifier_solver (btor);
      }
      else
      {
        btor->slv = btor_new_fun_solver (btor);
        // TODO (ma): make options for lod_limit and sat_limit
        BTOR_FUN_SOLVER (btor)->lod_limit = lod_limit;
        BTOR_FUN_SOLVER (btor)->sat_limit = sat_limit;
      }
    }

    assert (btor->slv);
    res = btor->slv->api.sat (btor->slv);
  }
  btor->last_sat_result = res;
  btor->btor_sat_btor_called++;
  btor->valid_assignments = 1;

  if (btor_opt_get (btor, BTOR_OPT_MODEL_GEN) && res == BTOR_RESULT_SAT)
  {
    switch (btor_opt_get (btor, BTOR_OPT_ENGINE))
    {
      case BTOR_ENGINE_SLS:
      case BTOR_ENGINE_PROP:
      case BTOR_ENGINE_AIGPROP:
        btor->slv->api.generate_model (
            btor->slv, btor_opt_get (btor, BTOR_OPT_MODEL_GEN) == 2, false);
        break;
      default:
        btor->slv->api.generate_model (
            btor->slv, btor_opt_get (btor, BTOR_OPT_MODEL_GEN) == 2, true);
    }
  }

#ifndef NDEBUG
  if (uclone)
  {
    assert (btor_opt_get (btor, BTOR_OPT_UCOPT));
    assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2);
    assert (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
    assert (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN));
    BtorSolverResult ucres = btor_check_sat (uclone, -1, -1);
    assert (res == ucres);
    btor_delete (uclone);
  }

  if (chkmodel)
  {
    if (res == BTOR_RESULT_SAT && !btor_opt_get (btor, BTOR_OPT_UCOPT))
    {
      btor_check_model (chkmodel);
    }
    btor_check_model_delete (chkmodel);
  }
#endif

#ifndef NDEBUG
  if (check && btor_opt_get (btor, BTOR_OPT_CHK_FAILED_ASSUMPTIONS)
      && !btor->inconsistent && btor->last_sat_result == BTOR_RESULT_UNSAT)
    btor_check_failed_assumptions (btor);
#endif

  delta = btor_util_time_stamp () - start;

  BTOR_MSG (btor->msg,
            1,
            "SAT call %d returned %d in %.3f seconds",
            btor->btor_sat_btor_called + 1,
            res,
            delta);

  btor->time.sat += delta;

  return res;
}

static bool
is_valid_argument (Btor *btor, BtorNode *exp)
{
  exp = btor_node_real_addr (exp);
  if (btor_node_is_fun (btor_simplify_exp (btor, exp))) return false;
  if (btor_node_is_array (btor_simplify_exp (btor, exp))) return false;
  /* scope of bound parmaters already closed (cannot be used anymore) */
  if (btor_node_is_param (exp) && btor_node_param_is_bound (exp)) return false;
  return true;
}

int32_t
btor_fun_sort_check (Btor *btor, BtorNode *args[], uint32_t argc, BtorNode *fun)
{
  (void) btor;
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);
  assert (btor_node_is_regular (fun));
  assert (btor_node_is_fun (btor_simplify_exp (btor, fun)));
  assert (argc == btor_node_fun_get_arity (btor, fun));

  uint32_t i;
  int32_t pos;
  BtorSortId sort;
  BtorTupleSortIterator it;

  assert (btor_sort_is_tuple (
      btor, btor_sort_fun_get_domain (btor, btor_node_get_sort_id (fun))));
  btor_iter_tuple_sort_init (
      &it, btor, btor_sort_fun_get_domain (btor, btor_node_get_sort_id (fun)));
  for (i = 0, pos = -1; i < argc; i++)
  {
    assert (btor_iter_tuple_sort_has_next (&it));
    sort = btor_iter_tuple_sort_next (&it);
    /* NOTE: we do not allow functions or arrays as arguments yet */
    if (!is_valid_argument (btor, args[i])
        || sort != btor_node_get_sort_id (args[i]))
    {
      pos = i;
      break;
    }
  }
  return pos;
}

static BtorAIG *
exp_to_aig (Btor *btor, BtorNode *exp)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *av;
  BtorAIG *result;

  assert (btor);
  assert (exp);
  assert (btor_node_bv_get_width (btor, exp) == 1);
  assert (!btor_node_real_addr (exp)->parameterized);

  amgr = btor_get_aig_mgr (btor);

  btor_synthesize_exp (btor, exp, 0);
  av = btor_node_real_addr (exp)->av;

  assert (av);
  assert (av->width == 1);

  result = av->aigs[0];

  if (btor_node_is_inverted (exp))
    result = btor_aig_not (amgr, result);
  else
    result = btor_aig_copy (amgr, result);

  return result;
}

BtorAIGVec *
btor_exp_to_aigvec (Btor *btor, BtorNode *exp, BtorPtrHashTable *backannotation)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGVec *result;

  assert (exp);

  avmgr = btor->avmgr;

  btor_synthesize_exp (btor, exp, backannotation);
  result = btor_node_real_addr (exp)->av;
  assert (result);

  if (btor_node_is_inverted (exp))
    result = btor_aigvec_not (avmgr, result);
  else
    result = btor_aigvec_copy (avmgr, result);

  return result;
}

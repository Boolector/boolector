/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2017 Armin Biere.
 *  Copyright (C) 2012-2018 Mathias Preiner.
 *  Copyright (C) 2012-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"

#include "btorclone.h"
#include "btorexp.h"
#include "btormodel.h"
#include "btorrewrite.h"
#include "btorslvaigprop.h"
#include "btorslvfun.h"
#include "btorslvprop.h"
#include "btorslvquant.h"
#include "btorslvsls.h"
#include "simplifier/btorack.h"
#include "simplifier/btorder.h"
#include "simplifier/btorelimapplies.h"
#include "simplifier/btorelimslices.h"
#include "simplifier/btorextract.h"
#include "simplifier/btormerge.h"
#include "simplifier/btorunconstrained.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
#include "simplifier/btorskel.h"
#endif
#include "btorabort.h"
#include "btorconfig.h"
#include "btordbg.h"
#include "btorlog.h"
#include "btoropt.h"

#include <limits.h>

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

#ifndef NDEBUG
static void check_model (Btor *, Btor *, BtorPtrHashTable *);
static BtorPtrHashTable *map_inputs_check_model (Btor *, Btor *);
static void check_failed_assumptions (Btor *);
#endif
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

  if (btor_opt_get (btor, BTOR_OPT_BETA_REDUCE_ALL))
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
  BTOR_INIT_STACK (mm, btor->failed_assumptions);
  btor->parameterized =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor->var_rhs = btor_hashptr_table_new (mm,
                                          (BtorHashPtr) btor_node_hash_by_id,
                                          (BtorCmpPtr) btor_node_compare_by_id);
  btor->fun_rhs = btor_hashptr_table_new (mm,
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

static void
delete_varsubst_constraints (Btor *btor)
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

  delete_varsubst_constraints (btor);

  btor_iter_hashptr_init (&it, btor->inputs);
  btor_iter_hashptr_queue (&it, btor->embedded_constraints);
  btor_iter_hashptr_queue (&it, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->assumptions);
  btor_iter_hashptr_queue (&it, btor->var_rhs);
  btor_iter_hashptr_queue (&it, btor->fun_rhs);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (btor, btor_iter_hashptr_next (&it));

  btor_hashptr_table_delete (btor->inputs);
  btor_hashptr_table_delete (btor->embedded_constraints);
  btor_hashptr_table_delete (btor->unsynthesized_constraints);
  btor_hashptr_table_delete (btor->synthesized_constraints);
  btor_hashptr_table_delete (btor->assumptions);
  for (i = 0; i < BTOR_COUNT_STACK (btor->failed_assumptions); i++)
  {
    if (BTOR_PEEK_STACK (btor->failed_assumptions, i))
      btor_node_release (btor, BTOR_PEEK_STACK (btor->failed_assumptions, i));
  }
  BTOR_RELEASE_STACK (btor->failed_assumptions);
  btor_hashptr_table_delete (btor->var_rhs);
  btor_hashptr_table_delete (btor->fun_rhs);

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
      if (btor_node_is_proxy (exp)) exp->simplified = 0;
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
    assert (bits->width == 1);
    if ((btor_node_is_inverted (exp) && btor_bv_get_bit (bits, 0))
        || (!btor_node_is_inverted (exp) && !btor_bv_get_bit (bits, 0)))
    {
      btor->inconsistent = true;
      return;
    }
    else
    {
      /* we do not add true */
      assert ((btor_node_is_inverted (exp) && !btor_bv_get_bit (bits, 0))
              || (!btor_node_is_inverted (exp) && btor_bv_get_bit (bits, 0)));
      return;
    }
  }

  uc = btor->unsynthesized_constraints;
  if (!btor_hashptr_table_get (uc, exp))
  {
    assert (!btor_hashptr_table_get (btor->embedded_constraints, exp));
    (void) btor_hashptr_table_add (uc, btor_node_copy (btor, exp));
    btor_node_real_addr (exp)->constraint = 1;
    btor->stats.constraints.unsynthesized++;
  }
}

static bool
is_embedded_constraint_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return btor_node_bv_get_width (btor, exp) == 1
         && btor_node_real_addr (exp)->parents > 0;
}

static void
insert_embedded_constraint (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!btor_node_real_addr (exp)->parameterized);
  assert (!btor_node_is_bv_const (exp));

  if (!btor_hashptr_table_get (btor->embedded_constraints, exp))
  {
    assert (!btor_hashptr_table_get (btor->unsynthesized_constraints, exp));
    (void) btor_hashptr_table_add (btor->embedded_constraints,
                                   btor_node_copy (btor, exp));
    btor_node_real_addr (exp)->constraint = 1;
    btor->stats.constraints.embedded++;
  }
}

static bool
constraint_is_inconsistent (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  //  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1);
  assert (btor_node_bv_get_width (btor, exp) == 1);

  BtorNode *rep;

  rep = btor_simplify_exp (btor, exp);

  return rep == btor_node_invert (rep)
         /* special case: top-level constraint applies are not simplified to
          * true/false (in order to not break dual prop) */
         || btor_hashptr_table_get (btor->synthesized_constraints,
                                    btor_node_invert (rep))
         || btor_hashptr_table_get (btor->unsynthesized_constraints,
                                    btor_node_invert (rep))
         || btor_hashptr_table_get (btor->embedded_constraints,
                                    btor_node_invert (rep));
}

static void
insert_into_constraint_tables (Btor *btor, BtorNode *exp)
{
  if (constraint_is_inconsistent (btor, exp))
    btor->inconsistent = true;
  else
  {
    if (!btor_node_real_addr (exp)->constraint)
    {
      if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1
          && is_embedded_constraint_exp (btor, exp)
          && !btor_node_is_bv_const (exp))
        insert_embedded_constraint (btor, exp);
      else
        btor_insert_unsynthesized_constraint (btor, exp);
    }
    else
    {
      assert (btor_hashptr_table_get (btor->unsynthesized_constraints, exp)
              || btor_hashptr_table_get (btor->embedded_constraints, exp));
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
             "add varsubst: %s -> %s",
             btor_util_node2string (left),
             btor_util_node2string (right));
    btor_hashptr_table_add (vsc, btor_node_copy (btor, left))->data.as_ptr =
        btor_node_copy (btor, right);
    /* do not set constraint flag, as they are gone after substitution
     * and treated differently */
    btor->stats.constraints.varsubst++;

    /* Always add varsubst contraints into unsynthesized/embedded contraints.
     * Otherwise, we get an inconsistent state if varsubst is disabled at
     * some point and not all varsubst constraints have been processed. */
    eq = btor_exp_eq (btor, left, right);
    insert_into_constraint_tables (btor, eq);
    btor_node_release (btor, eq);
  }
  /* if v = t_1 is already in varsubst, we
   * have to synthesize v = t_2 */
  else if (right != (BtorNode *) bucket->data.as_ptr)
  {
    eq = btor_exp_eq (btor, left, right);
    /* only add if it is not in a constraint table: can be already in
     * embedded or unsythesized constraints */
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

  is_cyclic = false;
  mm        = btor->mm;
  cache     = btor_hashint_table_new (mm);
  real_left = btor_node_real_addr (left);
  BTOR_INIT_QUEUE (mm, queue);

  cur = btor_node_real_addr (right);
  goto OCCURRENCE_CHECK_ENTER_WITHOUT_POP;

  do
  {
    cur = btor_node_real_addr (BTOR_DEQUEUE (queue));
  OCCURRENCE_CHECK_ENTER_WITHOUT_POP:
    assert (!btor_node_is_proxy (cur));
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
  BtorNode *const_exp, *real_exp;
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

  if (btor_node_is_bv_ult (exp)
      && (btor_node_is_bv_var (btor_node_real_addr (exp)->e[0])
          || btor_node_is_bv_var (btor_node_real_addr (exp)->e[1])))
  {
    real_exp = btor_node_real_addr (exp);

    if (btor_node_is_inverted (exp))
      comp = BTOR_SUBST_COMP_UGTE_KIND;
    else
      comp = BTOR_SUBST_COMP_ULT_KIND;

    if (btor_node_is_bv_var (real_exp->e[0]))
    {
      var   = real_exp->e[0];
      right = real_exp->e[1];
    }
    else
    {
      assert (btor_node_is_bv_var (real_exp->e[1]));
      var   = real_exp->e[1];
      right = real_exp->e[0];
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
    if (btor_hashptr_table_get (btor->varsubst_constraints, var)) return false;

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

  /* in the boolean case a != b is the same as a == ~b */
  if (btor_node_is_inverted (exp) && btor_node_is_bv_eq (exp)
      && btor_node_bv_get_width (btor, btor_node_real_addr (exp)->e[0]) == 1)
  {
    left  = btor_node_real_addr (exp)->e[0];
    right = btor_node_real_addr (exp)->e[1];

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

  left       = exp->e[0];
  right      = exp->e[1];
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
    assert (bits->width == 1);
    /* we do not add true/false */
    if ((btor_node_is_inverted (exp) && btor_bv_get_bit (bits, 0))
        || (!btor_node_is_inverted (exp) && !btor_bv_get_bit (bits, 0)))
      btor->inconsistent = true;
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
    /* NOTE: variable substitution constraints need to be added to either
     * unsynthesized or embedded constraints, as otherwise the constraint
     * flag won't be set, which might lead to an inconsistent state:
     * E.g.:
     *
     * assume (a0)
     *   -> a0->simplified = c0 (which is a constraint)
     *   -> adds true/false as assumption, since a0 simplified to c0
     * sat ()
     *   -> c0 gets simplified to c1 (c0->simplified = c1)
     *   -> c1 is a variable substitution constraint
     *   -> c1 is added to varsubst_constraints (no constraint flag set)
     *   -> simplify returns UNSAT before substituting all varsubst
     *      constraints
     *   -> sat returns UNSAT
     * failed (a0)
     *   -> a0->simplified = c1 (due to pointer chasing)
     *   -> c1 is not an assumption and thus, failed () aborts
     */
    insert_into_constraint_tables (btor, exp);
    report_constraint_stats (btor, false);
  }
}

void
btor_reset_assumptions (Btor *btor)
{
  assert (btor);

  BtorPtrHashTableIterator it;
  uint32_t i;

  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (btor, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (btor->assumptions);
  btor->assumptions =
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
    if (!btor_node_is_proxy (cur))
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

  /* Note: do not simplify constraint expression with btor_exp_simplify in order
   *       to prevent constraint expressions from not being added to
   *       btor->assumptions. */
  exp = btor_pointer_chase_simplified_exp (btor, exp);

  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!btor_hashptr_table_get (btor->assumptions, exp))
    (void) btor_hashptr_table_add (btor->assumptions,
                                   btor_node_copy (btor, exp));
}

bool
btor_is_assumption_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
  assert (exp);

  /* Note: do not simplify constraint expression in order to prevent
   *       constraint expressions from not being added to btor->assumptions. */
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return btor_hashptr_table_get (btor->assumptions, exp) ? true : false;
}

bool
btor_failed_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
  assert (btor->last_sat_result == BTOR_RESULT_UNSAT);
  assert (exp);
  assert (btor_is_assumption_exp (btor, exp));

  bool res;
  int32_t i, lit;
  double start;
  BtorAIG *aig;
  BtorNode *real_exp, *cur, *e;
  BtorNodePtrStack work_stack, assumptions;
  BtorSATMgr *smgr;
  BtorIntHashTable *mark;

  start = btor_util_time_stamp ();

  /* Note: do not simplify constraint expression in order to prevent
   *       constraint expressions from not being added to btor->assumptions. */
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_node_real_addr (exp)->btor == btor);
  assert (!btor_node_is_fun (exp));
  assert (btor_node_bv_get_width (btor, exp) == 1);
  assert (!btor_node_real_addr (exp)->parameterized);
  assert (btor_is_assumption_exp (btor, exp));
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
update_constraints (Btor *btor, BtorNode *exp)
{
  BtorPtrHashTable *unsynthesized_constraints, *synthesized_constraints;
  BtorPtrHashTable *embedded_constraints, *pos, *neg;
  BtorNode *simplified, *not_simplified, *not_exp;
  assert (btor);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (exp->simplified);
  assert (!btor_node_real_addr (exp->simplified)->simplified);
  assert (exp->constraint);
  assert (exp->refs > 1);
  assert (!exp->parameterized);
  assert (!btor_node_real_addr (exp->simplified)->parameterized);

  not_exp                   = btor_node_invert (exp);
  simplified                = exp->simplified;
  not_simplified            = btor_node_invert (simplified);
  embedded_constraints      = btor->embedded_constraints;
  unsynthesized_constraints = btor->unsynthesized_constraints;
  synthesized_constraints   = btor->synthesized_constraints;
  pos = neg = 0;

  if (btor_hashptr_table_get (unsynthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = unsynthesized_constraints;
  }

  if (btor_hashptr_table_get (unsynthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = unsynthesized_constraints;
  }

  if (btor_hashptr_table_get (embedded_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = embedded_constraints;
  }

  if (btor_hashptr_table_get (embedded_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = embedded_constraints;
  }

  if (btor_hashptr_table_get (synthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = synthesized_constraints;
  }

  if (btor_hashptr_table_get (synthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = synthesized_constraints;
  }

  if (pos)
  {
    btor_hashptr_table_remove (pos, exp, 0, 0);
    btor_node_release (btor, exp);
  }

  if (neg)
  {
    btor_hashptr_table_remove (neg, not_exp, 0, 0);
    btor_node_release (btor, not_exp);
  }

  exp->constraint = 0;
}

static void
set_simplified_exp (Btor *btor, BtorNode *exp, BtorNode *simplified)
{
  assert (btor);
  assert (exp);
  assert (simplified);
  assert (btor_node_is_regular (exp));
  assert (!btor_node_real_addr (simplified)->simplified);
  assert (exp->arity <= 3);
  assert (btor_node_get_sort_id (exp) == btor_node_get_sort_id (simplified));
  assert (exp->parameterized
          || !btor_node_real_addr (simplified)->parameterized);
  assert (!btor_node_real_addr (simplified)->parameterized
          || exp->parameterized);

  /* FIXME: indicator for slow-down in incremental mode, when too many
   * synthesized nodes are rewritten, it can significantly slow-down the
   * solver. */
  if (btor_node_is_synth (exp)) btor->stats.rewrite_synth++;

  if (exp->simplified) btor_node_release (btor, exp->simplified);

  exp->simplified = btor_node_copy (btor, simplified);

  if (exp->constraint) update_constraints (btor, exp);

  /* if a variable or UF gets simplified we need to save the original input
   * exp in a hash table (for model generation) */
  if (btor_node_is_bv_var (exp) && !btor_hashptr_table_get (btor->var_rhs, exp))
  {
    btor_hashptr_table_add (btor->var_rhs, btor_node_copy (btor, exp));
  }
  else if (btor_node_is_uf (exp)
           && !btor_hashptr_table_get (btor->fun_rhs, exp))
  {
    btor_hashptr_table_add (btor->fun_rhs, btor_node_copy (btor, exp));
  }

  btor_node_set_to_proxy (btor, exp);

  /* if simplified is parameterized, exp was also parameterized */
  if (btor_node_real_addr (simplified)->parameterized) exp->parameterized = 1;
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
    assert (btor_node_is_proxy (simplified));
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
    set_simplified_exp (btor, cur, invert ? not_simplified : simplified);
    btor_node_release (btor, cur);
    cur = next;
  } while (btor_node_real_addr (cur)->simplified);
  btor_node_release (btor, cur);

  /* if starting expression is inverted, then we have to invert result */
  if (btor_node_is_inverted (exp)) simplified = btor_node_invert (simplified);

  return simplified;
}

BtorNode *
btor_pointer_chase_simplified_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp;

  assert (btor);
  assert (exp);
  (void) btor;

  real_exp = btor_node_real_addr (exp);

  /* no simplified expression ? */
  if (!real_exp->simplified) return exp;

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

  if (btor_hashptr_table_get (btor->embedded_constraints, real_exp))
  {
    result = btor->true_exp;
  }
  else if (btor_hashptr_table_get (btor->embedded_constraints, not_exp))
  {
    result = btor_node_invert (btor->true_exp);
  }
  else if (btor_hashptr_table_get (btor->unsynthesized_constraints, real_exp))
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

  result = btor_pointer_chase_simplified_exp (btor, exp);

  /* NOTE: embedded constraints rewriting is enabled with rwl > 1 */
  if (btor_opt_get (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS)
      && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1
      && btor_node_real_addr (result)->constraint)
    return simplify_constraint_exp (btor, result);

  assert (btor_node_real_addr (result)->btor == btor);
  assert (btor_node_real_addr (result)->refs > 0);

  return result;
}

/*------------------------------------------------------------------------*/

/* update hash tables of nodes in order to get rid of proxy nodes
 */
static void
update_node_hash_tables (Btor *btor)
{
  BtorNode *cur, *data, *key, *simp_key, *simp_data;
  BtorPtrHashTableIterator it, iit;
  BtorPtrHashTable *static_rho, *new_static_rho;

  /* update static_rhos */
  btor_iter_hashptr_init (&it, btor->lambdas);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur        = btor_iter_hashptr_next (&it);
    static_rho = btor_node_lambda_get_static_rho (cur);

    if (!static_rho) continue;

    new_static_rho =
        btor_hashptr_table_new (btor->mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
    /* update static rho to get rid of proxy nodes */
    btor_iter_hashptr_init (&iit, static_rho);
    while (btor_iter_hashptr_has_next (&iit))
    {
      data = iit.bucket->data.as_ptr;
      key  = btor_iter_hashptr_next (&iit);
      assert (btor_node_is_regular (key));
      simp_key  = btor_simplify_exp (btor, key);
      simp_data = btor_simplify_exp (btor, data);

      if (!btor_hashptr_table_get (new_static_rho, simp_key))
      {
        btor_hashptr_table_add (new_static_rho, btor_node_copy (btor, simp_key))
            ->data.as_ptr = btor_node_copy (btor, simp_data);
      }
      btor_node_release (btor, key);
      btor_node_release (btor, data);
    }
    btor_hashptr_table_delete (static_rho);
    btor_node_lambda_set_static_rho (cur, new_static_rho);
  }
}

static BtorNode *
rebuild_binder_exp (Btor *btor, BtorNode *exp)
{
  assert (btor_node_is_regular (exp));
  assert (btor_node_is_binder (exp));
  assert (!btor_node_param_get_assigned_exp (exp->e[0]));

  BtorNode *result;

  /* we need to reset the binding lambda here as otherwise it is not possible
   * to create a new lambda term with the same param that substitutes 'exp' */
  btor_node_param_set_binder (exp->e[0], 0);
  if (btor_node_is_forall (exp))
    result = btor_exp_forall (btor, exp->e[0], exp->e[1]);
  else if (btor_node_is_exists (exp))
    result = btor_exp_exists (btor, exp->e[0], exp->e[1]);
  else
  {
    assert (btor_node_is_lambda (exp));
    result = btor_exp_lambda (btor, exp->e[0], exp->e[1]);
  }

  /* binder not rebuilt, set binder again */
  if (result == exp) btor_node_param_set_binder (exp->e[0], exp);

  return result;
}

static BtorNode *
rebuild_lambda_exp (Btor *btor, BtorNode *exp)
{
  assert (btor_node_is_regular (exp));
  assert (btor_node_is_lambda (exp));
  assert (!btor_node_param_get_assigned_exp (exp->e[0]));

  BtorNode *result;

  result = rebuild_binder_exp (btor, exp);

  /* copy static_rho for new lambda */
  if (btor_node_lambda_get_static_rho (exp)
      && !btor_node_lambda_get_static_rho (result))
    btor_node_lambda_set_static_rho (
        result, btor_node_lambda_copy_static_rho (btor, exp));
  if (exp->is_array) result->is_array = 1;
  return result;
}

static BtorNode *
rebuild_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_is_regular (exp));

  switch (exp->kind)
  {
    case BTOR_PROXY_NODE:
    case BTOR_CONST_NODE:
    case BTOR_VAR_NODE:
    case BTOR_PARAM_NODE:
    case BTOR_UF_NODE:
      return btor_node_copy (btor, btor_simplify_exp (btor, exp));
    case BTOR_BV_SLICE_NODE:
      return btor_exp_bv_slice (btor,
                                exp->e[0],
                                btor_node_bv_slice_get_upper (exp),
                                btor_node_bv_slice_get_lower (exp));
    case BTOR_LAMBDA_NODE: return rebuild_lambda_exp (btor, exp);
    case BTOR_EXISTS_NODE:
    case BTOR_FORALL_NODE: return rebuild_binder_exp (btor, exp);
    default: return btor_exp_create (btor, exp->kind, exp->e, exp->arity);
  }
}

/* we perform all variable substitutions in one pass and rebuild the formula
 * cyclic substitutions must have been deleted before! */
static void
substitute_vars_and_rebuild_exps (Btor *btor, BtorPtrHashTable *substs)
{
  assert (btor);
  assert (substs);

  BtorNodePtrStack stack, root_stack;
  BtorPtrHashBucket *b;
  BtorNode *cur, *cur_parent, *rebuilt_exp, **temp, **top, *rhs, *simplified;
  BtorMemMgr *mm;
  BtorPtrHashTableIterator it;
  BtorNodeIterator nit;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  bool ispushed;
  uint32_t i;

  if (substs->count == 0u) return;

  mm   = btor->mm;
  mark = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, root_stack);
  /* search upwards for all reachable roots */
  /* we push all left sides on the search stack */
  btor_iter_hashptr_init (&it, substs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (btor_node_is_regular (cur));
    assert (btor_node_is_bv_var (cur) || btor_node_is_uf (cur));
    BTOR_PUSH_STACK (stack, cur);
  }

  do
  {
    assert (!BTOR_EMPTY_STACK (stack));
    cur = BTOR_POP_STACK (stack);
    assert (btor_node_is_regular (cur));
    if (!btor_hashint_map_contains (mark, cur->id))
    {
      btor_hashint_map_add (mark, cur->id);
      btor_iter_parent_init (&nit, cur);
      /* are we at a root ? */
      ispushed = false;
      while (btor_iter_parent_has_next (&nit))
      {
        cur_parent = btor_iter_parent_next (&nit);
        assert (btor_node_is_regular (cur_parent));
        ispushed = true;
        BTOR_PUSH_STACK (stack, cur_parent);
      }
      if (!ispushed) BTOR_PUSH_STACK (root_stack, btor_node_copy (btor, cur));
    }
  } while (!BTOR_EMPTY_STACK (stack));

  /* copy roots on substitution stack */
  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    BTOR_PUSH_STACK (stack, *temp);

  /* substitute */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (stack));

    d = btor_hashint_map_get (mark, cur->id);
    if (!d) continue;

    assert (!btor_node_is_bv_const (cur));

    if (d->as_int == 0)
    {
      BTOR_PUSH_STACK (stack, cur);
      d->as_int = 1;
      if (btor_node_is_bv_var (cur) || btor_node_is_uf (cur))
      {
        b = btor_hashptr_table_get (substs, cur);
        assert (b);
        assert (cur == (BtorNode *) b->key);
        rhs = (BtorNode *) b->data.as_ptr;
        assert (rhs);
        BTOR_PUSH_STACK (stack, rhs);
      }
      else
      {
        for (i = 1; i <= cur->arity; i++)
          BTOR_PUSH_STACK (stack, cur->e[cur->arity - i]);
      }
    }
    else
    {
      assert (d->as_int == 1);
      btor_hashint_map_remove (mark, cur->id, 0);
      if (btor_node_is_bv_var (cur) || btor_node_is_uf (cur))
      {
        b = btor_hashptr_table_get (substs, cur);
        assert (b);
        assert (cur == (BtorNode *) b->key);
        rhs = (BtorNode *) b->data.as_ptr;
        assert (rhs);
        rebuilt_exp = btor_node_copy (btor, rhs);
        if (btor_node_is_bv_var (cur))
          btor->stats.var_substitutions++;
        else
          btor->stats.uf_substitutions++;
      }
      else
        rebuilt_exp = rebuild_exp (btor, cur);
      assert (rebuilt_exp);
      assert (rebuilt_exp != cur);

      simplified = btor_simplify_exp (btor, rebuilt_exp);
      set_simplified_exp (btor, cur, simplified);
      btor_node_release (btor, rebuilt_exp);
    }
  }

  BTOR_RELEASE_STACK (stack);

  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    btor_node_release (btor, *temp);
  BTOR_RELEASE_STACK (root_stack);

  update_node_hash_tables (btor);
  btor_hashint_map_delete (mark);
  assert (btor_dbg_check_lambdas_static_rho_proxy_free (btor));
}

static void
substitute_var_exps (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *varsubst_constraints, *order, *substs;
  BtorNode *cur, *constraint, *left, *right, *child;
  BtorPtrHashBucket *b, *b_temp;
  BtorPtrHashTableIterator it;
  int32_t order_num, val, max;
  uint32_t i;
  BtorNodePtrStack stack;
  double start, delta;
  uint32_t count;
  BtorMemMgr *mm;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  mm                   = btor->mm;
  varsubst_constraints = btor->varsubst_constraints;

  if (varsubst_constraints->count == 0u) return;

  start = btor_util_time_stamp ();

  BTOR_INIT_STACK (mm, stack);

  /* new equality constraints may be added during rebuild */
  count = 0;
  while (varsubst_constraints->count > 0u)
  {
    order_num = 1;
    order     = btor_hashptr_table_new (mm,
                                    (BtorHashPtr) btor_node_hash_by_id,
                                    (BtorCmpPtr) btor_node_compare_by_id);

    substs = btor_hashptr_table_new (mm,
                                     (BtorHashPtr) btor_node_hash_by_id,
                                     (BtorCmpPtr) btor_node_compare_by_id);

    /* we copy the current substitution constraints into a local hash table,
     * and empty the global substitution table */
    while (varsubst_constraints->count > 0u)
    {
      count++;
      b   = varsubst_constraints->first;
      cur = (BtorNode *) b->key;
      assert (btor_node_is_regular (cur));
      assert (btor_node_is_bv_var (cur) || btor_node_is_uf (cur));
      right = (BtorNode *) b->data.as_ptr;
      /* NOTE: we need to update 'right' here, since 'right' might have
       * already been rebuilt in merge_lambdas (in beta reduction part) */
      btor_hashptr_table_add (substs, cur)->data.as_ptr =
          btor_node_copy (btor, btor_simplify_exp (btor, right));
      btor_node_release (btor, right);
      btor_hashptr_table_remove (varsubst_constraints, cur, 0, 0);
    }
    assert (varsubst_constraints->count == 0u);

    mark = btor_hashint_table_new (mm);
    /* we search for cyclic substitution dependencies
     * and map the substitutions to an ordering number */
    btor_iter_hashptr_init (&it, substs);
    while (btor_iter_hashptr_has_next (&it))
    {
      cur = btor_iter_hashptr_next (&it);
      assert (btor_node_is_regular (cur));
      assert (btor_node_is_bv_var (cur) || btor_node_is_uf (cur));
      BTOR_PUSH_STACK (stack, cur);

      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = btor_node_real_addr (BTOR_POP_STACK (stack));

        if (!cur)
        {
          cur = BTOR_POP_STACK (stack); /* left */
          assert (btor_node_is_regular (cur));
          assert (btor_node_is_bv_var (cur) || btor_node_is_uf (cur));
          assert (!btor_hashptr_table_get (order, cur));
          btor_hashptr_table_add (order, cur)->data.as_int = order_num++;
          continue;
        }
        /* visited (DFS) */
        if (btor_hashint_table_contains (mark, cur->id)) continue;

        btor_hashint_table_add (mark, cur->id);

        if (btor_node_is_bv_const (cur) || btor_node_is_bv_var (cur)
            || btor_node_is_param (cur) || btor_node_is_uf (cur))
        {
          b_temp = btor_hashptr_table_get (substs, cur);
          if (b_temp)
          {
            BTOR_PUSH_STACK (stack, cur); /* left  */
            BTOR_PUSH_STACK (stack, 0);
            BTOR_PUSH_STACK (stack, /* right */
                             (BtorNode *) b_temp->data.as_ptr);
          }
          else
          {
            assert (!btor_hashptr_table_get (order, cur));
            btor_hashptr_table_add (order, cur)->data.as_int = 0;
          }
        }
        else
        {
          assert (cur->arity >= 1);
          assert (cur->arity <= 3);
          for (i = 1; i <= cur->arity; i++)
            BTOR_PUSH_STACK (stack, cur->e[cur->arity - i]);
        }
      }
    }

    btor_hashint_table_delete (mark);
    mark = btor_hashint_map_new (mm);

    /* we look for cycles */
    btor_iter_hashptr_init (&it, substs);
    while (btor_iter_hashptr_has_next (&it))
    {
      b   = it.bucket;
      cur = btor_iter_hashptr_next (&it);
      assert (btor_node_is_regular (cur));
      assert (btor_node_is_bv_var (cur) || btor_node_is_uf (cur));
      BTOR_PUSH_STACK (stack, (BtorNode *) b->data.as_ptr);

      /* we assume that there are no direct loops
       * as a result of occurrence check */
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = btor_node_real_addr (BTOR_POP_STACK (stack));
        d   = btor_hashint_map_get (mark, cur->id);

        if (d && d->as_int == 1) /* cur has max order of its children */
          continue;

        if (btor_node_is_bv_const (cur) || btor_node_is_bv_var (cur)
            || btor_node_is_param (cur) || btor_node_is_uf (cur))
        {
          assert (btor_hashptr_table_get (order, cur));
          continue;
        }

        assert (cur->arity >= 1);
        assert (cur->arity <= 3);

        if (!d)
        {
          btor_hashint_map_add (mark, cur->id);
          BTOR_PUSH_STACK (stack, cur);
          for (i = 1; i <= cur->arity; i++)
            BTOR_PUSH_STACK (stack, cur->e[cur->arity - i]);
        }
        else /* cur is visited, its children are visited */
        {
          /* compute maximum of children */
          assert (d->as_int == 0);
          d->as_int = 1;
          max       = 0;
          for (i = 1; i <= cur->arity; i++)
          {
            child  = btor_node_real_addr (cur->e[cur->arity - i]);
            b_temp = btor_hashptr_table_get (order, child);
            assert (b_temp);
            val = b_temp->data.as_int;
            assert (val >= 0);
            max = BTOR_MAX_UTIL (max, val);
          }
          btor_hashptr_table_add (order, cur)->data.as_int = max;
        }
      }
    }
    btor_hashint_map_delete (mark);

    assert (BTOR_EMPTY_STACK (stack));
    /* we eliminate cyclic substitutions, and reset mark flags */
    btor_iter_hashptr_init (&it, substs);
    while (btor_iter_hashptr_has_next (&it))
    {
      right = (BtorNode *) it.bucket->data.as_ptr;
      assert (right);
      left = btor_iter_hashptr_next (&it);
      assert (btor_node_is_regular (left));
      assert (btor_node_is_bv_var (left) || btor_node_is_uf (left));
      b_temp = btor_hashptr_table_get (order, left);
      assert (b_temp);
      order_num = b_temp->data.as_int;
      b_temp    = btor_hashptr_table_get (order, btor_node_real_addr (right));
      assert (b_temp);
      max = b_temp->data.as_int;
      assert (order_num != max);
      /* found cycle */
      if (max > order_num) BTOR_PUSH_STACK (stack, left);
    }

    /* we delete cyclic substitutions and synthesize them instead */
    while (!BTOR_EMPTY_STACK (stack))
    {
      left = BTOR_POP_STACK (stack);
      assert (btor_node_is_regular (left));
      assert (btor_node_is_bv_var (left) || btor_node_is_uf (left));
      right = (BtorNode *) btor_hashptr_table_get (substs, left)->data.as_ptr;
      assert (right);

      constraint = btor_exp_eq (btor, left, right);
      /* only add if it is not in a constraint table: can be already in
       * embedded or unsythesized constraints */
      if (!btor_node_real_addr (constraint)->constraint)
        btor_insert_unsynthesized_constraint (btor, constraint);
      btor_node_release (btor, constraint);

      btor_hashptr_table_remove (substs, left, 0, 0);
      btor_node_release (btor, left);
      btor_node_release (btor, right);
    }

    /* we rebuild and substiute variables in one pass */
    substitute_vars_and_rebuild_exps (btor, substs);

    /* cleanup, we delete all substitution constraints */
    btor_iter_hashptr_init (&it, substs);
    while (btor_iter_hashptr_has_next (&it))
    {
      right = (BtorNode *) it.bucket->data.as_ptr;
      assert (right);
      left = btor_iter_hashptr_next (&it);
      assert (btor_node_is_regular (left));
      assert (btor_node_is_proxy (left));
      assert (left->simplified);
      btor_node_release (btor, left);
      btor_node_release (btor, right);
    }

    btor_hashptr_table_delete (order);
    btor_hashptr_table_delete (substs);
  }

  BTOR_RELEASE_STACK (stack);
  delta = btor_util_time_stamp () - start;
  btor->time.subst += delta;
  BTOR_MSG (
      btor->msg, 1, "%d variables substituted in %.1f seconds", count, delta);
}

static bool
all_exps_below_rebuilt (Btor *btor, BtorNode *exp, BtorIntHashTable *mark)
{
  assert (btor);
  assert (exp);
  assert (mark);

  uint32_t i;
  BtorNode *cur;

  cur = btor_find_substitution (btor, exp);
  if (cur)
  {
    cur = btor_simplify_exp (btor, cur);
    return !btor_hashint_map_contains (mark, btor_node_real_addr (cur)->id);
  }

  exp = btor_node_real_addr (exp);
  for (i = 0; i < exp->arity; i++)
  {
    cur = btor_node_real_addr (btor_simplify_exp (btor, exp->e[i]));
    if (btor_hashint_map_contains (mark, cur->id)) return false;
  }

  return true;
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

static void
substitute_and_rebuild (Btor *btor, BtorPtrHashTable *subst)
{
  assert (btor);
  assert (subst);

  uint32_t i;
  double start;
  BtorMemMgr *mm;
  BtorNode *cur, *cur_parent, *rebuilt_exp, *simplified, *sub;
  BtorNodePtrStack roots;
  BtorNodePtrQueue queue;
  BtorPtrHashTableIterator hit;
  BtorNodeIterator it;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  if (subst->count == 0u) return;

  start = btor_util_time_stamp ();
  mm    = btor->mm;

  mark = btor_hashint_map_new (mm);
  BTOR_INIT_STACK (mm, roots);
  BTOR_INIT_QUEUE (mm, queue);

  btor_iter_hashptr_init (&hit, subst);
  while (btor_iter_hashptr_has_next (&hit))
  {
    cur = btor_node_real_addr (btor_iter_hashptr_next (&hit));
    BTOR_ENQUEUE (queue, cur);
  }

  /* mark cone and copy roots */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (btor_node_is_regular (cur));
    assert (!btor_node_is_proxy (cur));

    if (!btor_hashint_map_contains (mark, cur->id))
    {
      btor_hashint_map_add (mark, cur->id);

      if (cur->parents == 0)
        BTOR_PUSH_STACK (roots, btor_node_copy (btor, cur));

      btor_iter_parent_init (&it, cur);
      while (btor_iter_parent_has_next (&it))
      {
        cur_parent = btor_iter_parent_next (&it);
        BTOR_ENQUEUE (queue, cur_parent);
      }
    }
  }

  btor_iter_hashptr_init (&hit, subst);
  while (btor_iter_hashptr_has_next (&hit))
  {
    cur = btor_node_real_addr (btor_iter_hashptr_next (&hit));
    d   = btor_hashint_map_get (mark, cur->id);
    assert (d);
    BTOR_ENQUEUE (queue, btor_node_copy (btor, cur));
    d->as_int = 1; /* mark as enqueued */
  }

  /* rebuild bottom-up */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (btor_node_is_regular (cur));
    assert (!btor_node_is_proxy (cur));
    assert (btor_hashint_map_contains (mark, cur->id));
    assert (btor_hashint_map_get (mark, cur->id)->as_int == 1);

    if (cur->refs == 1)
    {
      btor_node_release (btor, cur);
      continue;
    }

    if (all_exps_below_rebuilt (btor, cur, mark))
    {
      btor_hashint_map_remove (mark, cur->id, 0);
      btor_node_release (btor, cur);

      /* traverse upwards and enqueue all parents that are not yet
       * in the queue. */
      btor_iter_parent_init (&it, cur);
      while (btor_iter_parent_has_next (&it))
      {
        cur_parent = btor_iter_parent_next (&it);
        d          = btor_hashint_map_get (mark, cur_parent->id);
        if (d && d->as_int == 1) continue;
        assert (!d || d->as_int == 0);
        if (!d) d = btor_hashint_map_add (mark, cur_parent->id);
        d->as_int = 1;
        BTOR_ENQUEUE (queue, btor_node_copy (btor, cur_parent));
      }

      if ((sub = btor_find_substitution (btor, cur)))
        rebuilt_exp = btor_node_copy (btor, sub);
      else
        rebuilt_exp = rebuild_exp (btor, cur);

      assert (btor_node_get_sort_id (cur)
              == btor_node_get_sort_id (rebuilt_exp));
      assert (rebuilt_exp);
      if (rebuilt_exp != cur)
      {
        simplified = btor_simplify_exp (btor, rebuilt_exp);
        // TODO: only push new roots? use hash table for roots instead of
        // stack?
        if (cur->parents == 0)
          BTOR_PUSH_STACK (roots, btor_node_copy (btor, cur));

        set_simplified_exp (btor, cur, simplified);
      }
      btor_node_release (btor, rebuilt_exp);
    }
    /* not all children rebuilt, enqueue again */
    else
      BTOR_ENQUEUE (queue, cur);
  }

  BTOR_RELEASE_QUEUE (queue);

  for (i = 0; i < BTOR_COUNT_STACK (roots); i++)
  {
    cur = BTOR_PEEK_STACK (roots, i);
    btor_node_release (btor, cur);
  }

  BTOR_RELEASE_STACK (roots);

  assert (btor_dbg_check_unique_table_children_proxy_free (btor));
  btor_hashint_map_delete (mark);

  update_node_hash_tables (btor);
  assert (btor_dbg_check_lambdas_static_rho_proxy_free (btor));
  btor->time.subst_rebuild += btor_util_time_stamp () - start;
}

void
btor_substitute_and_rebuild (Btor *btor, BtorPtrHashTable *substs)
{
  substitute_and_rebuild (btor, substs);
}

static void
substitute_embedded_constraints (Btor *btor)
{
  assert (btor);

  BtorPtrHashTableIterator it;
  BtorNode *cur;

  btor_iter_hashptr_init (&it, btor->embedded_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (btor_node_real_addr (cur)->constraint);
    /* embedded constraints have possibly lost their parents,
     * e.g. top conjunction of constraints that are released */
    if (btor_node_real_addr (cur)->parents > 0) btor->stats.ec_substitutions++;
  }

  substitute_and_rebuild (btor, btor->embedded_constraints);
}

static void
process_embedded_constraints (Btor *btor)
{
  assert (btor);

  BtorPtrHashTableIterator it;
  BtorNodePtrStack ec;
  double start, delta;
  BtorNode *cur;
  uint32_t count;

  if (btor->embedded_constraints->count > 0u)
  {
    start = btor_util_time_stamp ();
    count = 0;
    BTOR_INIT_STACK (btor->mm, ec);
    btor_iter_hashptr_init (&it, btor->embedded_constraints);
    while (btor_iter_hashptr_has_next (&it))
    {
      cur = btor_node_copy (btor, btor_iter_hashptr_next (&it));
      BTOR_PUSH_STACK (ec, cur);
    }

    /* Note: it may happen that new embedded constraints are inserted into
     *       btor->embedded_constraints here. */
    substitute_embedded_constraints (btor);

    while (!BTOR_EMPTY_STACK (ec))
    {
      cur = BTOR_POP_STACK (ec);

      if (btor_hashptr_table_get (btor->embedded_constraints, cur))
      {
        count++;
        btor_hashptr_table_remove (btor->embedded_constraints, cur, 0, 0);
        btor_insert_unsynthesized_constraint (btor, cur);
        btor_node_release (btor, cur);
      }
      btor_node_release (btor, cur);
    }
    BTOR_RELEASE_STACK (ec);

    delta = btor_util_time_stamp () - start;
    btor->time.embedded += delta;
    BTOR_MSG (btor->msg,
              1,
              "replaced %u embedded constraints in %1.f seconds",
              count,
              delta);
  }
}

/*------------------------------------------------------------------------*/

static void
update_assumptions (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *ass;
  BtorNode *cur, *simp;
  BtorPtrHashTableIterator it;

  ass = btor_hashptr_table_new (btor->mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    if (btor_node_real_addr (cur)->simplified)
    {
      /* Note: do not simplify constraint expression in order to prevent
       * constraint expressions from not being added to btor->assumptions.
       */
      simp = btor_pointer_chase_simplified_exp (btor, cur);
      if (!btor_hashptr_table_get (ass, simp))
        btor_hashptr_table_add (ass, btor_node_copy (btor, simp));
      btor_node_release (btor, cur);
    }
    else
    {
      if (!btor_hashptr_table_get (ass, cur))
        btor_hashptr_table_add (ass, cur);
      else
        btor_node_release (btor, cur);
    }
  }
  btor_hashptr_table_delete (btor->assumptions);
  btor->assumptions = ass;
}

int32_t
btor_simplify (Btor *btor)
{
  assert (btor);

  BtorSolverResult result;
  uint32_t rounds;
  double start, delta;
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  uint32_t skelrounds = 0;
#endif

  rounds = 0;
  start  = btor_util_time_stamp ();

  if (btor->inconsistent) goto DONE;

  /* empty varsubst_constraints table if variable substitution was disabled
   * after adding variable substitution constraints (they are still in
   * unsynthesized_constraints).
   */
  if (btor_opt_get (btor, BTOR_OPT_VAR_SUBST) == 0
      && btor->varsubst_constraints->count > 0)
  {
    delete_varsubst_constraints (btor);
    btor->varsubst_constraints =
        btor_hashptr_table_new (btor->mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
  }

  do
  {
    rounds++;
    assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
    assert (btor_dbg_check_all_hash_tables_simp_free (btor));
    assert (btor_dbg_check_unique_table_children_proxy_free (btor));
    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1)
    {
      if (btor_opt_get (btor, BTOR_OPT_VAR_SUBST))
      {
        substitute_var_exps (btor);
        assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
        assert (btor_dbg_check_all_hash_tables_simp_free (btor));
        assert (btor_dbg_check_unique_table_children_proxy_free (btor));

        if (btor->inconsistent) break;

        if (btor->varsubst_constraints->count)
          break;  // TODO (ma): continue instead of break?
      }

      process_embedded_constraints (btor);
      assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
      assert (btor_dbg_check_all_hash_tables_simp_free (btor));
      assert (btor_dbg_check_unique_table_children_proxy_free (btor));

      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) continue;
    }

    if (btor_opt_get (btor, BTOR_OPT_ELIMINATE_SLICES)
        && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && !btor_opt_get (btor, BTOR_OPT_INCREMENTAL))
    {
      btor_eliminate_slices_on_bv_vars (btor);
      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count
          || btor->embedded_constraints->count)
        continue;
    }

#ifndef BTOR_DO_NOT_PROCESS_SKELETON
    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_opt_get (btor, BTOR_OPT_SKELETON_PREPROC))
    {
      skelrounds++;
      if (skelrounds <= 1)  // TODO only one?
      {
        btor_process_skeleton (btor);
        assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
        assert (btor_dbg_check_all_hash_tables_simp_free (btor));
        assert (btor_dbg_check_unique_table_children_proxy_free (btor));
        if (btor->inconsistent) break;
      }

      if (btor->varsubst_constraints->count
          || btor->embedded_constraints->count)
        continue;
    }
#endif

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    if (btor_opt_get (btor, BTOR_OPT_UCOPT)
        && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && !btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
        && !btor_opt_get (btor, BTOR_OPT_MODEL_GEN))
    {
      btor_optimize_unconstrained (btor);
      assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
      assert (btor_dbg_check_all_hash_tables_simp_free (btor));
      assert (btor_dbg_check_unique_table_children_proxy_free (btor));
      if (btor->inconsistent) break;
    }

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_opt_get (btor, BTOR_OPT_EXTRACT_LAMBDAS))
      btor_extract_lambdas (btor);

    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_opt_get (btor, BTOR_OPT_MERGE_LAMBDAS))
      btor_merge_lambdas (btor);

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    /* rewrite/beta-reduce applies on lambdas */
    if (btor_opt_get (btor, BTOR_OPT_BETA_REDUCE_ALL))
      btor_eliminate_applies (btor);

    /* add ackermann constraints for all uninterpreted functions */
    if (btor_opt_get (btor, BTOR_OPT_ACKERMANN))
      btor_add_ackermann_constraints (btor);
  } while (btor->varsubst_constraints->count
           || btor->embedded_constraints->count);

DONE:
  delta = btor_util_time_stamp () - start;
  btor->time.simplify += delta;
  BTOR_MSG (btor->msg, 1, "%u rewriting rounds in %.1f seconds", rounds, delta);

  if (btor->inconsistent)
    result = BTOR_RESULT_UNSAT;
  else if (btor->unsynthesized_constraints->count == 0u
           && btor->synthesized_constraints->count == 0u)
    result = BTOR_RESULT_SAT;
  else
    result = BTOR_RESULT_UNKNOWN;

  BTOR_MSG (btor->msg, 1, "simplification returned %d", result);
  update_assumptions (btor);
  return result;
}

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
    assert (!btor_node_is_proxy (exp));

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
    assert (!btor_node_real_addr (cur)->simplified);
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

#ifndef NDEBUG
  // NOTE: disable checking if quantifiers present for now (not supported yet)
  if (btor->quantifiers->count) check = false;

  Btor *uclone = 0;
  if (check && btor_opt_get (btor, BTOR_OPT_CHK_UNCONSTRAINED)
      && btor_opt_get (btor, BTOR_OPT_UCOPT)
      && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
      && !btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
      && !btor_opt_get (btor, BTOR_OPT_MODEL_GEN))
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

  Btor *mclone             = 0;
  BtorPtrHashTable *inputs = 0;
  if (check && btor_opt_get (btor, BTOR_OPT_CHK_MODEL))
  {
    mclone = btor_clone_exp_layer (btor, 0);
    btor_opt_set (mclone, BTOR_OPT_LOGLEVEL, 0);
    btor_opt_set (mclone, BTOR_OPT_VERBOSITY, 0);
    btor_opt_set (mclone, BTOR_OPT_FUN_DUAL_PROP, 0);
    btor_opt_set (mclone, BTOR_OPT_CHK_UNCONSTRAINED, 0);
    btor_opt_set (mclone, BTOR_OPT_CHK_MODEL, 0);
    btor_opt_set (mclone, BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0);
    btor_set_term (mclone, 0, 0);

    btor_opt_set (mclone, BTOR_OPT_ENGINE, BTOR_ENGINE_FUN);
    if (mclone->slv)
    {
      mclone->slv->api.delet (mclone->slv);
      mclone->slv = 0;
    }

    inputs = map_inputs_check_model (btor, mclone);

    // NOTE: cadical does not support incremental mode, which is required for
    // checking the model. we need to switch to lingeling.
#ifdef BTOR_USE_CADICAL
    if (btor_opt_get (mclone, BTOR_OPT_SAT_ENGINE) == BTOR_SAT_ENGINE_CADICAL)
    {
#ifdef BTOR_USE_LINGELING
      btor_opt_set (mclone, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_LINGELING);
#else
      btor_delete_substitutions (mclone);
      BtorPtrHashTableIterator it;
      btor_iter_hashptr_init (&it, inputs);
      while (btor_iter_hashptr_has_next (&it))
      {
        btor_node_release (btor, (BtorNode *) it.bucket->data.as_ptr);
        btor_node_release (mclone, btor_iter_hashptr_next (&it));
      }
      btor_hashptr_table_delete (inputs);
      btor_delete (mclone);
      mclone = 0;
#endif
    }
#endif
  }
#endif

#ifndef NBTORLOG
  btor_opt_log_opts (btor);
#endif

  /* set option based on formula characteristics */

  /* eliminate lambdas (define-fun) in the QF_BV case */
  if (btor->ufs->count == 0 && btor->feqs->count == 0
      && btor->lambdas->count > 0)
    btor_opt_set (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

  // FIXME (ma): not sound with slice elimination. see red-vsl.proof3106.smt2
  /* disabling slice elimination is better on QF_ABV and BV */
  if (btor->ufs->count > 0 || btor->quantifiers->count > 0)
    btor_opt_set (btor, BTOR_OPT_ELIMINATE_SLICES, 0);
  /* set options for quantifiers */
  if (btor->quantifiers->count > 0)
  {
    btor_opt_set (btor, BTOR_OPT_UCOPT, 0);
    btor_opt_set (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
  }

  /* FIXME: disable options that potentially slow down incremental mode */
  if (btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
      && !btor_opt_get (btor, BTOR_OPT_INCREMENTAL_RW))
  {
    /* variable substitution and skeleton preprocessing can have the effect
     * that already bit-blased structures get rewritten, which have to
     * be bit-blasted again */
    btor_opt_set (btor, BTOR_OPT_VAR_SUBST, 0);
    btor_opt_set (btor, BTOR_OPT_SKELETON_PREPROC, 0);
    btor_opt_set (btor, BTOR_OPT_EXTRACT_LAMBDAS, 0);
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
                || btor_opt_get (btor, BTOR_OPT_BETA_REDUCE_ALL));
        btor->slv = btor_new_sls_solver (btor);
      }
      else if (engine == BTOR_ENGINE_PROP && btor->ufs->count == 0
               && btor->feqs->count == 0)
      {
        assert (btor->lambdas->count == 0
                || btor_opt_get (btor, BTOR_OPT_BETA_REDUCE_ALL));
        btor->slv = btor_new_prop_solver (btor);
      }
      else if (engine == BTOR_ENGINE_AIGPROP && btor->ufs->count == 0
               && btor->feqs->count == 0)
      {
        assert (btor->lambdas->count == 0
                || btor_opt_get (btor, BTOR_OPT_BETA_REDUCE_ALL));
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

    /* 'btor->assertions' contains all assertions that were asserted in context
     * levels > 0 (boolector_push). We assume all these assertions on every
     * btor_check_sat call since these assumptions are valid until the
     * corresponding context is popped. */
    if (BTOR_COUNT_STACK (btor->assertions) > 0)
    {
      assert (BTOR_COUNT_STACK (btor->assertions_trail) > 0);
      uint32_t i;
      for (i = 0; i < BTOR_COUNT_STACK (btor->assertions); i++)
        btor_assume_exp (btor, BTOR_PEEK_STACK (btor->assertions, i));
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

  if (mclone)
  {
    assert (inputs);
    if (res == BTOR_RESULT_SAT && !btor_opt_get (btor, BTOR_OPT_UCOPT))
    {
      if (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN))
      {
        switch (btor_opt_get (btor, BTOR_OPT_ENGINE))
        {
          case BTOR_ENGINE_SLS:
          case BTOR_ENGINE_PROP:
          case BTOR_ENGINE_AIGPROP:
            btor->slv->api.generate_model (btor->slv, false, false);
            break;
          default: btor->slv->api.generate_model (btor->slv, false, true);
        }
      }
      mclone->cbs.term.fun   = 0;
      mclone->cbs.term.state = 0;
      mclone->cbs.term.done  = 0;
      check_model (btor, mclone, inputs);
    }

    BtorPtrHashTableIterator it;
    btor_iter_hashptr_init (&it, inputs);
    while (btor_iter_hashptr_has_next (&it))
    {
      btor_node_release (btor, (BtorNode *) it.bucket->data.as_ptr);
      btor_node_release (mclone, btor_iter_hashptr_next (&it));
    }
    btor_hashptr_table_delete (inputs);
    btor_delete (mclone);
  }
#endif

#ifndef NDEBUG
  if (check && btor_opt_get (btor, BTOR_OPT_CHK_FAILED_ASSUMPTIONS)
      && !btor->inconsistent && btor->last_sat_result == BTOR_RESULT_UNSAT)
    check_failed_assumptions (btor);
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

#ifndef NDEBUG
BtorPtrHashTable *
map_inputs_check_model (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);

  BtorNode *cur;
  BtorPtrHashBucket *b;
  BtorPtrHashTableIterator it;
  BtorPtrHashTable *inputs;

  inputs = btor_hashptr_table_new (clone->mm,
                                   (BtorHashPtr) btor_node_hash_by_id,
                                   (BtorCmpPtr) btor_node_compare_by_id);

  btor_iter_hashptr_init (&it, clone->bv_vars);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    b   = btor_hashptr_table_get (btor->bv_vars, cur);
    assert (b);

    assert (!btor_hashptr_table_get (inputs, cur));
    btor_hashptr_table_add (inputs, btor_node_copy (clone, cur))->data.as_ptr =
        btor_node_copy (btor, (BtorNode *) b->key);
  }

  btor_iter_hashptr_init (&it, clone->ufs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    b   = btor_hashptr_table_get (btor->ufs, cur);
    assert (b);

    assert (!btor_hashptr_table_get (inputs, cur));
    btor_hashptr_table_add (inputs, btor_node_copy (clone, cur))->data.as_ptr =
        btor_node_copy (btor, (BtorNode *) b->key);
  }

  return inputs;
}

static void
rebuild_formula (Btor *btor, uint32_t rewrite_level)
{
  assert (btor);

  uint32_t i, cnt;
  BtorNode *cur;
  BtorPtrHashTable *t;

  /* set new rewrite level */
  btor_opt_set (btor, BTOR_OPT_REWRITE_LEVEL, rewrite_level);

  t = btor_hashptr_table_new (btor->mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);

  /* collect all leaves and rebuild whole formula */
  for (i = 1, cnt = BTOR_COUNT_STACK (btor->nodes_id_table); i <= cnt; i++)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, cnt - i))) continue;

    if (btor_node_is_proxy (cur)) continue;

    if (cur->arity == 0)
    {
      assert (btor_node_is_bv_var (cur) || btor_node_is_bv_const (cur)
              || btor_node_is_param (cur) || btor_node_is_uf (cur));
      btor_hashptr_table_add (t, cur);
    }
  }

  substitute_and_rebuild (btor, t);
  btor_hashptr_table_delete (t);
}

static void
check_model (Btor *btor, Btor *clone, BtorPtrHashTable *inputs)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_RESULT_SAT);
  assert (clone);
  assert (inputs);

  uint32_t i;
  int32_t ret;
  BtorNode *cur, *exp, *simp, *simp_clone, *real_simp_clone, *model, *eq;
  BtorNode *args, *apply;
  BtorPtrHashTableIterator it;
  const BtorPtrHashTable *fmodel;
  BtorBitVector *value;
  BtorBitVectorTuple *args_tuple;
  BtorNodePtrStack consts;

  /* formula did not change since last sat call, we have to reset assumptions
   * from the previous run */
  if (clone->valid_assignments) btor_reset_incremental_usage (clone);

  /* add assumptions as assertions */
  btor_iter_hashptr_init (&it, clone->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    btor_assert_exp (clone, btor_iter_hashptr_next (&it));
  btor_reset_assumptions (clone);

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0) substitute_var_exps (clone);

  /* rebuild formula with new rewriting level */
  rebuild_formula (clone, 3);

  /* add bit vector variable models */
  BTOR_INIT_STACK (clone->mm, consts);
  btor_iter_hashptr_init (&it, inputs);
  while (btor_iter_hashptr_has_next (&it))
  {
    exp = (BtorNode *) it.bucket->data.as_ptr;
    assert (exp);
    assert (btor_node_is_regular (exp));
    assert (exp->btor == btor);
    /* Note: we do not want simplified constraints here */
    simp = btor_pointer_chase_simplified_exp (btor, exp);
    cur  = btor_iter_hashptr_next (&it);
    assert (btor_node_is_regular (cur));
    assert (cur->btor == clone);
    simp_clone      = btor_simplify_exp (clone, cur);
    real_simp_clone = btor_node_real_addr (simp_clone);

    if (btor_node_is_fun (real_simp_clone))
    {
      fmodel = btor_model_get_fun (btor, simp);
      if (!fmodel) continue;

      BTORLOG (
          2, "assert model for %s", btor_util_node2string (real_simp_clone));
      btor_iter_hashptr_init (&it, (BtorPtrHashTable *) fmodel);
      while (btor_iter_hashptr_has_next (&it))
      {
        value      = (BtorBitVector *) it.bucket->data.as_ptr;
        args_tuple = btor_iter_hashptr_next (&it);

        /* create condition */
        assert (BTOR_EMPTY_STACK (consts));
        for (i = 0; i < args_tuple->arity; i++)
        {
          model = btor_exp_bv_const (clone, args_tuple->bv[i]);
          BTOR_PUSH_STACK (consts, model);
        }

        args  = btor_exp_args (clone, consts.start, BTOR_COUNT_STACK (consts));
        apply = btor_exp_apply (clone, real_simp_clone, args);
        model = btor_exp_bv_const (clone, value);
        eq    = btor_exp_eq (clone, apply, model);
        btor_assert_exp (clone, eq);
        btor_node_release (clone, eq);
        btor_node_release (clone, model);
        btor_node_release (clone, apply);
        btor_node_release (clone, args);

        while (!BTOR_EMPTY_STACK (consts))
          btor_node_release (clone, BTOR_POP_STACK (consts));
      }
    }
    else
    {
      /* we need to invert the assignment if simplified is inverted */
      model =
          btor_exp_bv_const (clone,
                          (BtorBitVector *) btor_model_get_bv (
                              btor, btor_node_cond_invert (simp_clone, simp)));
      BTORLOG (2,
               "assert model for %s (%s) [%s]",
               btor_util_node2string (real_simp_clone),
               btor_node_get_symbol (clone, cur),
               btor_util_node2string (model));

      eq = btor_exp_eq (clone, real_simp_clone, model);
      btor_assert_exp (clone, eq);
      btor_node_release (clone, eq);
      btor_node_release (clone, model);
    }
  }
  BTOR_RELEASE_STACK (consts);

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0) substitute_var_exps (clone);

  btor_opt_set (clone, BTOR_OPT_BETA_REDUCE_ALL, 1);
  ret = btor_simplify (clone);

  // btor_print_model (btor, "btor", stdout);
  assert (ret != BTOR_RESULT_UNKNOWN
          || btor_check_sat (clone, -1, -1) == BTOR_RESULT_SAT);
  // TODO: check if roots have been simplified through aig rewriting
  // BTOR_ABORT (ret == BTOR_RESULT_UNKNOWN, "rewriting needed");
  BTOR_ABORT (ret == BTOR_RESULT_UNSAT, "invalid model");
}
#endif

#ifndef NDEBUG
static void
check_failed_assumptions (Btor *btor)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_RESULT_UNSAT);

  Btor *clone;
  BtorNode *ass, *cass;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack stack;

  clone = btor_clone_exp_layer (btor, 0);
  btor_opt_set (clone, BTOR_OPT_LOGLEVEL, 0);
  btor_opt_set (clone, BTOR_OPT_VERBOSITY, 0);
  btor_opt_set (clone, BTOR_OPT_FUN_DUAL_PROP, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_UNCONSTRAINED, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_MODEL, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0);
  btor_set_term (clone, 0, 0);

  btor_opt_set (clone, BTOR_OPT_ENGINE, BTOR_ENGINE_FUN);
  assert (clone->slv);
  clone->slv->api.delet (clone->slv);
  clone->slv = 0;

  /* assert failed assumptions */
  BTOR_INIT_STACK (btor->mm, stack);
  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    ass = btor_iter_hashptr_next (&it);
    if (btor_failed_exp (btor, ass))
    {
      cass = btor_node_match (clone, ass);
      assert (cass);
      BTOR_PUSH_STACK (stack, cass);
    }
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    cass = BTOR_POP_STACK (stack);
    btor_assert_exp (clone, cass);
    btor_node_release (clone, cass);
  }
  BTOR_RELEASE_STACK (stack);

  /* cleanup assumptions */
  btor_iter_hashptr_init (&it, clone->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (clone, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (clone->assumptions);
  clone->assumptions =
      btor_hashptr_table_new (clone->mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);

  assert (btor_check_sat (clone, -1, -1) == BTOR_RESULT_UNSAT);
  btor_delete (clone);
}
#endif

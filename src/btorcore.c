/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *  Copyright (C) 2012-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"

#include "btorclone.h"
#include "btormodel.h"
#include "btorrewrite.h"
#include "btorslvaigprop.h"
#include "btorslvfun.h"
#include "btorslvprop.h"
#include "btorslvsls.h"
#include "simplifier/btorack.h"
#include "simplifier/btorelimapplies.h"
#include "simplifier/btorelimslices.h"
#include "simplifier/btorextract.h"
#include "simplifier/btormerge.h"
#include "simplifier/btorunconstrained.h"
#include "utils/btorexpiter.h"
#include "utils/btorhashint.h"
#include "utils/btormisc.h"
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
  ((BtorAIG *) (((unsigned long int) (exp) &1ul) ^ ((unsigned long int) (aig))))

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
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

void
btor_delete_substitutions (Btor *btor)
{
  assert (btor);

  BtorNode *cur;
  BtorPtrHashTableIterator it;

  btor_init_ptr_hash_table_iterator (&it, btor->substitutions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    btor_release_exp (btor, (BtorNode *) it.bucket->data.as_ptr);
    cur = btor_next_ptr_hash_table_iterator (&it);
    btor_release_exp (btor, cur);
  }

  btor_delete_ptr_hash_table (btor->substitutions);
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
    b = btor_get_ptr_hash_table (btor->substitutions,
                                 BTOR_REAL_ADDR_NODE (exp));
    if (!b) break;
    result = BTOR_COND_INVERT_NODE (exp, (BtorNode *) b->data.as_ptr);
    exp    = result;
  }

  return result;
}

#ifndef NDEBUG
static int
substitution_cycle_check_dbg (Btor *btor, BtorNode *exp, BtorNode *subst)
{
  int i, cycle = 0;
  BtorMemMgr *mm;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;

  mm    = btor->mm;
  exp   = BTOR_REAL_ADDR_NODE (exp);
  cache = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, subst);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cache, cur->id)) continue;

    if (cur == exp)
    {
      cycle = 1;
      break;
    }

    btor_add_int_hash_table (cache, cur->id);

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }
  BTOR_RELEASE_STACK (visit);
  btor_delete_int_hash_table (cache);
  return !cycle;
}
#endif

void
btor_insert_substitution (Btor *btor,
                          BtorNode *exp,
                          BtorNode *subst,
                          int update)
{
  assert (btor);
  assert (exp);
  assert (subst);
  assert (btor->substitutions);
  assert (update == 0 || update == 1);
  assert (btor_exp_get_sort_id (exp) == btor_exp_get_sort_id (subst));

  BtorNode *simp;
  BtorPtrHashBucket *b;
  exp = BTOR_REAL_ADDR_NODE (exp);

  if (exp == BTOR_REAL_ADDR_NODE (subst)) return;

  assert (substitution_cycle_check_dbg (btor, exp, subst));

  b = btor_get_ptr_hash_table (btor->substitutions, exp);
  if (update && b)
  {
    assert (b->data.as_ptr);
    /* release data of current bucket */
    btor_release_exp (btor, (BtorNode *) b->data.as_ptr);
    btor_remove_ptr_hash_table (btor->substitutions, exp, 0, 0);
    /* release key of current bucket */
    btor_release_exp (btor, exp);
  }
  else if (b)
  {
    assert ((BtorNode *) b->data.as_ptr == subst);
    /* substitution already inserted */
    return;
  }

  simp = btor_find_substitution (btor, subst);

  if (simp) subst = simp;

  assert (!btor_get_ptr_hash_table (btor->substitutions,
                                    BTOR_REAL_ADDR_NODE (subst)));

  if (exp == BTOR_REAL_ADDR_NODE (subst)) return;

  btor_add_ptr_hash_table (btor->substitutions, btor_copy_exp (btor, exp))
      ->data.as_ptr = btor_copy_exp (btor, subst);
}

/*------------------------------------------------------------------------*/

const char *
btor_version (const Btor *btor)
{
  assert (btor);
  (void) btor;
  return BTOR_VERSION;
}

BtorMemMgr *
btor_get_mem_mgr_btor (const Btor *btor)
{
  assert (btor);
  return btor->mm;
}
BtorAIGMgr *
btor_get_aig_mgr_btor (const Btor *btor)
{
  assert (btor);
  return btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
}

BtorSATMgr *
btor_get_sat_mgr_btor (const Btor *btor)
{
  assert (btor);
  return btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_btor (btor));
}

void
btor_reset_time_btor (Btor *btor)
{
  assert (btor);
  BTOR_CLR (&btor->time);
}

void
btor_reset_stats_btor (Btor *btor)
{
  assert (btor);
#ifndef NDEBUG
  if (btor->stats.rw_rules_applied)
    btor_delete_ptr_hash_table (btor->stats.rw_rules_applied);
#endif
  BTOR_CLR (&btor->stats);
  assert (!btor->stats.rw_rules_applied);
#ifndef NDEBUG
  btor->stats.rw_rules_applied = btor_new_ptr_hash_table (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
#endif
}

static int
constraints_stats_changes (Btor *btor)
{
  int res;

  if (btor->stats.oldconstraints.varsubst && !btor->varsubst_constraints->count)
    return INT_MAX;

  if (btor->stats.oldconstraints.embedded && !btor->embedded_constraints->count)
    return INT_MAX;

  if (btor->stats.oldconstraints.unsynthesized
      && !btor->unsynthesized_constraints->count)
    return INT_MAX;

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
report_constraint_stats (Btor *btor, int force)
{
  int changes;

  if (!force)
  {
    if (btor_get_opt (btor, BTOR_OPT_VERBOSITY) <= 0) return;

    changes = constraints_stats_changes (btor);

    if (btor_get_opt (btor, BTOR_OPT_VERBOSITY) == 1 && changes < 100000)
      return;

    if (btor_get_opt (btor, BTOR_OPT_VERBOSITY) == 2 && changes < 1000) return;

    if (btor_get_opt (btor, BTOR_OPT_VERBOSITY) == 3 && changes < 10) return;

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
static int
number_of_ops (Btor *btor)
{
  int i, result;
  assert (btor);

  result = 0;
  for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++) result += btor->ops[i].cur;

  return result;
}

static double
percent (double a, double b)
{
  return b ? 100.0 * a / b : 0.0;
}

void
btor_print_stats_btor (Btor *btor)
{
  int num_final_ops, verbosity, i;

  if (!btor) return;

  verbosity = btor_get_opt (btor, BTOR_OPT_VERBOSITY);

  report_constraint_stats (btor, 1);
  if (btor_get_opt (btor, BTOR_OPT_UCOPT))
  {
    BTOR_MSG (
        btor->msg, 1, "unconstrained bv props: %d", btor->stats.bv_uc_props);
    BTOR_MSG (btor->msg,
              1,
              "unconstrained array props: %d",
              btor->stats.fun_uc_props);
    BTOR_MSG (btor->msg,
              1,
              "unconstrained parameterized props: %d",
              btor->stats.param_uc_props);
  }
  BTOR_MSG (btor->msg,
            1,
            "variable substitutions: %d",
            btor->stats.var_substitutions);
  BTOR_MSG (btor->msg,
            1,
            "uninterpreted function substitutions: %d",
            btor->stats.uf_substitutions);
  BTOR_MSG (btor->msg,
            1,
            "embedded constraint substitutions: %d",
            btor->stats.ec_substitutions);
  BTOR_MSG (btor->msg, 1, "assumptions: %u", btor->assumptions->count);

  if (verbosity > 0)
  {
    BTOR_MSG (btor->msg, 2, "max rec. RW: %d", btor->stats.max_rec_rw_calls);
    BTOR_MSG (btor->msg,
              2,
              "number of expressions ever created: %lld",
              btor->stats.expressions);
    num_final_ops = number_of_ops (btor);
    assert (num_final_ops >= 0);
    BTOR_MSG (btor->msg, 2, "number of final expressions: %d", num_final_ops);
    assert (sizeof g_btor_op2str / sizeof *g_btor_op2str == BTOR_NUM_OPS_NODE);

    BTOR_MSG (btor->msg,
              1,
              "memory allocated for nodes: %.2f MB",
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
  }

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "bit blasting statistics:");
  BTOR_MSG (btor->msg,
            1,
            " AIG vectors (cur/max): %lld/%lld",
            btor->avmgr ? btor->avmgr->cur_num_aigvecs : 0,
            btor->avmgr ? btor->avmgr->max_num_aigvecs : 0);
  BTOR_MSG (btor->msg,
            1,
            " AIG ANDs (cur/max): %lld/%lld",
            btor->avmgr ? btor->avmgr->amgr->cur_num_aigs : 0,
            btor->avmgr ? btor->avmgr->amgr->max_num_aigs : 0);
  BTOR_MSG (btor->msg,
            1,
            " AIG variables: %lld",
            btor->avmgr ? btor->avmgr->amgr->max_num_aig_vars : 0);
  BTOR_MSG (btor->msg,
            1,
            " CNF variables: %lld",
            btor->avmgr ? btor->avmgr->amgr->num_cnf_vars : 0);
  BTOR_MSG (btor->msg,
            1,
            " CNF clauses: %lld",
            btor->avmgr ? btor->avmgr->amgr->num_cnf_clauses : 0);
  BTOR_MSG (btor->msg,
            1,
            " CNF literals: %lld",
            btor->avmgr ? btor->avmgr->amgr->num_cnf_literals : 0);

  BTOR_MSG (btor->msg, 1, "");
#ifndef NDEBUG
  BtorPtrHashTableIterator it;
  char *rule;
  int num = 0;
  BTOR_MSG (btor->msg, 1, "applied rewriting rules:");
  btor_init_ptr_hash_table_iterator (&it, btor->stats.rw_rules_applied);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    num  = it.bucket->data.as_int;
    rule = btor_next_ptr_hash_table_iterator (&it);
    BTOR_MSG (btor->msg, 1, "  %s: %d", rule, num);
  }
#endif
  BTOR_MSG (btor->msg,
            1,
            "linear constraint equations: %d",
            btor->stats.linear_equations);
  BTOR_MSG (btor->msg,
            1,
            "gaussian elimination in linear equations: %d",
            btor->stats.gaussian_eliminations);
  BTOR_MSG (btor->msg,
            1,
            "eliminated sliced variables: %d",
            btor->stats.eliminated_slices);
  BTOR_MSG (btor->msg,
            1,
            "extracted skeleton constraints: %d",
            btor->stats.skeleton_constraints);
  BTOR_MSG (
      btor->msg, 1, "and normalizations: %d", btor->stats.ands_normalized);
  BTOR_MSG (
      btor->msg, 1, "add normalizations: %d", btor->stats.adds_normalized);
  BTOR_MSG (
      btor->msg, 1, "mul normalizations: %d", btor->stats.muls_normalized);
  BTOR_MSG (btor->msg, 1, "lambdas merged: %lld", btor->stats.lambdas_merged);
  BTOR_MSG (btor->msg,
            1,
            "apply propagation during construction: %d",
            btor->stats.apply_props_construct);
  BTOR_MSG (
      btor->msg, 1, "beta reductions: %lld", btor->stats.beta_reduce_calls);
  BTOR_MSG (btor->msg, 1, "clone calls: %lld", btor->stats.clone_calls);

  if (btor->slv) btor->slv->api.print_stats (btor->slv);

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
  BTOR_MSG (btor->msg, 1, "%.2f seconds for cloning", btor->time.cloning);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds substitute and rebuild",
            btor->time.subst_rebuild);
  if (btor_get_opt (btor, BTOR_OPT_UCOPT))
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds for unconstrained optimization",
              btor->time.ucopt);
  if (btor_get_opt (btor, BTOR_OPT_MODEL_GEN))
    BTOR_MSG (
        btor->msg, 1, "%.2f seconds model generation", btor->time.model_gen);
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (
      btor->msg, 1, "%.2f seconds in rewriting engine", btor->time.rewrite);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds in variable substitution during rewriting (%.0f%%)",
            btor->time.subst,
            percent (btor->time.subst, btor->time.rewrite));
  BTOR_MSG (
      btor->msg,
      1,
      "%.2f seconds in embedded constraint replacing during rewriting (%.0f%%)",
      btor->time.embedded,
      percent (btor->time.embedded, btor->time.rewrite));
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds in apply elimination during rewriting (%.0f%%)",
            btor->time.elimapplies,
            percent (btor->time.elimapplies, btor->time.rewrite));
  if (btor_get_opt (btor, BTOR_OPT_ELIMINATE_SLICES))
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds in slicing during rewriting (%.0f%%)",
              btor->time.slicing,
              percent (btor->time.slicing, btor->time.rewrite));
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds skeleton preprocessing during rewriting (%.0f%%)",
            btor->time.skel,
            percent (btor->time.skel, btor->time.rewrite));
#endif

  if (btor->slv) btor->slv->api.print_time_stats (btor->slv);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (
      btor->msg, 1, "%.1f MB", btor->mm->maxallocated / (double) (1 << 20));
}

Btor *
btor_new_btor (void)
{
  BtorMemMgr *mm;
  Btor *btor;

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, btor);

  btor->mm  = mm;
  btor->msg = btor_new_btor_msg (btor);
  btor_set_msg_prefix_btor (btor, "btor");

  BTOR_INIT_UNIQUE_TABLE (mm, btor->nodes_unique_table);
  BTOR_INIT_SORT_UNIQUE_TABLE (mm, btor->sorts_unique_table);
  BTOR_INIT_STACK (btor->mm, btor->nodes_id_table);
  BTOR_PUSH_STACK (btor->nodes_id_table, 0);
  BTOR_INIT_STACK (btor->mm, btor->functions_with_model);

  btor_init_opts (btor);

  btor->avmgr = btor_new_aigvec_mgr (btor);

  btor_init_rng (&btor->rng, btor_get_opt (btor, BTOR_OPT_SEED));

  btor->bv_assignments  = btor_new_bv_assignment_list (mm);
  btor->fun_assignments = btor_new_array_assignment_list (mm);

  btor->symbols = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor->node2symbol =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);

  btor->inputs  = btor_new_ptr_hash_table (mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  btor->bv_vars = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
  btor->ufs     = btor_new_ptr_hash_table (mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  btor->lambdas = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
  btor->feqs    = btor_new_ptr_hash_table (mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);

  btor->valid_assignments = 1;

  btor->varsubst_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->embedded_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->unsynthesized_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->synthesized_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->assumptions =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->parameterized =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->var_rhs = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
  btor->fun_rhs = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
#ifndef NDEBUG
  btor->stats.rw_rules_applied = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
#endif

  btor->true_exp = btor_true_exp (btor);

  return btor;
}

static int
terminate_aux_btor (void *btor)
{
  assert (btor);

  int res;
  Btor *bt;

  bt = (Btor *) btor;
  if (!bt->cbs.term.fun) return 0;
  if (bt->cbs.term.done) return 1;
  res = ((int (*) (void *)) bt->cbs.term.fun) (bt->cbs.term.state);
  if (res) bt->cbs.term.done = res;
  return res;
}

int
btor_terminate_btor (Btor *btor)
{
  assert (btor);

  if (btor->cbs.term.termfun) return btor->cbs.term.termfun (btor);
  return 0;
}

void
btor_set_term_btor (Btor *btor, int (*fun) (void *), void *state)
{
  assert (btor);

  BtorSATMgr *smgr;

  btor->cbs.term.termfun = terminate_aux_btor;
  btor->cbs.term.fun     = fun;
  btor->cbs.term.state   = state;

  smgr = btor_get_sat_mgr_btor (btor);
  if (btor_has_term_support_sat_mgr (smgr))
    btor_set_term_sat_mgr (smgr, terminate_aux_btor, btor);
}

static void
release_all_ext_exp_refs (Btor *btor)
{
  assert (btor);

  int i;
  BtorNode *exp;

  for (i = BTOR_COUNT_STACK (btor->nodes_id_table) - 1; i >= 0; i--)
  {
    if (!(exp = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;
    if (exp->ext_refs)
    {
      assert (exp->ext_refs <= exp->refs);
      exp->refs = exp->refs - exp->ext_refs + 1;
      btor->external_refs -= exp->ext_refs;
      assert (exp->refs > 0);
      exp->ext_refs = 0;
      btor_release_exp (btor, exp);
    }
  }
}

static void
release_all_ext_sort_refs (Btor *btor)
{
  assert (btor);

  int i;
  BtorSort *sort;

  for (i = BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort) - 1; i >= 0; i--)
  {
    sort = BTOR_PEEK_STACK (btor->sorts_unique_table.id2sort, i);
    if (!sort) continue;
    assert (sort->refs);
    assert (sort->ext_refs <= sort->refs);
    sort->refs = sort->refs - sort->ext_refs + 1;
    btor->external_refs -= sort->ext_refs;
    assert (sort->refs > 0);
    sort->ext_refs = 0;
    btor_release_sort (btor, sort->id);
  }
}

void
btor_release_all_ext_refs (Btor *btor)
{
  release_all_ext_exp_refs (btor);
  release_all_ext_sort_refs (btor);
}

void
btor_delete_btor (Btor *btor)
{
  assert (btor);

  int i;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorNode *exp;
  BtorPtrHashTableIterator it;

  mm = btor->mm;

  if (btor->slv) btor->slv->api.delet (btor->slv);

  if (btor->parse_error_msg) btor_freestr (mm, btor->parse_error_msg);

  btor_delete_bv_assignment_list (
      btor->bv_assignments,
      btor_get_opt (btor, BTOR_OPT_AUTO_CLEANUP)
          || btor_get_opt (btor, BTOR_OPT_AUTO_CLEANUP_INTERNAL));
  btor_delete_array_assignment_list (
      btor->fun_assignments,
      btor_get_opt (btor, BTOR_OPT_AUTO_CLEANUP)
          || btor_get_opt (btor, BTOR_OPT_AUTO_CLEANUP_INTERNAL));

  btor_init_ptr_hash_table_iterator (&it, btor->varsubst_constraints);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    btor_release_exp (btor, it.bucket->data.as_ptr);
    exp = btor_next_ptr_hash_table_iterator (&it);
    btor_release_exp (btor, exp);
  }
  btor_delete_ptr_hash_table (btor->varsubst_constraints);

  btor_init_ptr_hash_table_iterator (&it, btor->inputs);
  btor_queue_ptr_hash_table_iterator (&it, btor->embedded_constraints);
  btor_queue_ptr_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&it, btor->assumptions);
  btor_queue_ptr_hash_table_iterator (&it, btor->var_rhs);
  btor_queue_ptr_hash_table_iterator (&it, btor->fun_rhs);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_ptr_hash_table_iterator (&it));

  btor_delete_ptr_hash_table (btor->inputs);
  btor_delete_ptr_hash_table (btor->embedded_constraints);
  btor_delete_ptr_hash_table (btor->unsynthesized_constraints);
  btor_delete_ptr_hash_table (btor->synthesized_constraints);
  btor_delete_ptr_hash_table (btor->assumptions);
  btor_delete_ptr_hash_table (btor->var_rhs);
  btor_delete_ptr_hash_table (btor->fun_rhs);

  btor_delete_model (btor);
  btor_release_exp (btor, btor->true_exp);

  for (i = 0; i < BTOR_COUNT_STACK (btor->functions_with_model); i++)
    btor_release_exp (btor, btor->functions_with_model.start[i]);
  BTOR_RELEASE_STACK (btor->functions_with_model);

  BTOR_INIT_STACK (mm, stack);
  btor_init_ptr_hash_table_iterator (&it, btor->lambdas);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    exp = btor_next_ptr_hash_table_iterator (&it);
    btor_lambda_delete_static_rho (btor, exp);
  }

  while (!BTOR_EMPTY_STACK (stack))
    btor_release_exp (btor, BTOR_POP_STACK (stack));
  BTOR_RELEASE_STACK (stack);

  if (btor_get_opt (btor, BTOR_OPT_AUTO_CLEANUP) && btor->external_refs)
    release_all_ext_exp_refs (btor);

  if (btor_get_opt (btor, BTOR_OPT_AUTO_CLEANUP_INTERNAL))
  {
    for (i = BTOR_COUNT_STACK (btor->nodes_id_table) - 1; i >= 0; i--)
    {
      exp = BTOR_PEEK_STACK (btor->nodes_id_table, i);
      if (!exp) continue;
      if (btor_is_proxy_node (exp)) exp->simplified = 0;
      assert (exp->refs);
      exp->refs = 1;
      btor->external_refs -= exp->ext_refs;
      exp->ext_refs = 0;
      btor_release_exp (btor, exp);
      assert (!BTOR_PEEK_STACK (btor->nodes_id_table, i));
    }
  }

  if (btor_get_opt (btor, BTOR_OPT_AUTO_CLEANUP) && btor->external_refs)
    release_all_ext_sort_refs (btor);

  assert (btor->external_refs == 0);

#ifndef NDEBUG
  bool node_leak = false;
  BtorNode *cur;
  /* we need to check id_table here as not all nodes are in the unique table */
  for (i = 0; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
    if (cur)
    {
      BTORLOG (1, "  unreleased node: %s (%d)", node2string (cur), cur->refs);
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

  btor_delete_ptr_hash_table (btor->node2symbol);
  btor_init_ptr_hash_table_iterator (&it, btor->symbols);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    btor_freestr (btor->mm, (char *) btor_next_ptr_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (btor->symbols);

  btor_delete_ptr_hash_table (btor->bv_vars);
  btor_delete_ptr_hash_table (btor->ufs);
  btor_delete_ptr_hash_table (btor->lambdas);
  btor_delete_ptr_hash_table (btor->feqs);
  btor_delete_ptr_hash_table (btor->parameterized);
#ifndef NDEBUG
  btor_delete_ptr_hash_table (btor->stats.rw_rules_applied);
#endif

  if (btor->avmgr) btor_delete_aigvec_mgr (btor->avmgr);
  btor_delete_opts (btor);

  assert (btor->rec_rw_calls == 0);
  btor_delete_btor_msg (btor->msg);
  BTOR_DELETE (mm, btor);
  btor_delete_mem_mgr (mm);
}

void
btor_set_msg_prefix_btor (Btor *btor, const char *prefix)
{
  assert (btor);

  btor_freestr (btor->mm, btor->msg->prefix);
  btor->msg->prefix = prefix ? btor_strdup (btor->mm, prefix) : (char *) prefix;
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
  amgr = btor_get_aig_mgr_btor (btor);

  while (uc->count > 0)
  {
    bucket = uc->first;
    assert (bucket);
    cur = (BtorNode *) bucket->key;

#ifndef NDEBUG
    if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 2)
    {
      BtorNode *real_cur = BTOR_REAL_ADDR_NODE (cur);
      if (btor_is_bv_eq_node (real_cur))
      {
#if 0
	      BtorNode * left = real_cur->e[0];
	      BtorNode * right = real_cur->e[1];
	      BtorNode * other;

	      if (btor_is_bv_const_node (left))
		other = right;
	      else if (btor_is_bv_const_node (right))
		other = left;
	      else
		other = 0;

	      // FIXME fails with symbolic lemmas (during beta-reduction
	      // rewrite level is forced to 1, hence symbolic lemmas might
	      // not be simplified as much as possible). possible solution:
	      // use rewrite level > 1 for lemma generation.
	      //if (other 
	      //    && !BTOR_IS_INVERTED_NODE (other) 
	      //    && btor_is_add_node (other))
	      //  {
	      //    assert (!btor_is_bv_const_node (other->e[0]));
	      //    assert (!btor_is_bv_const_node (other->e[1]));
	      //  }
#endif
      }
    }
#endif

    if (!btor_get_ptr_hash_table (sc, cur))
    {
      aig = exp_to_aig (btor, cur);
      if (aig == BTOR_AIG_FALSE)
      {
        btor->found_constraint_false = true;
        break;
      }
      btor_add_toplevel_aig_to_sat (amgr, aig);
      btor_release_aig (amgr, aig);
      (void) btor_add_ptr_hash_table (sc, cur);
      btor_remove_ptr_hash_table (uc, cur, 0, 0);

      btor->stats.constraints.synthesized++;
      report_constraint_stats (btor, 0);
    }
    else
    {
      /* constraint is already in sc */
      btor_remove_ptr_hash_table (uc, cur, 0, 0);
      btor_release_exp (btor, cur);
    }
  }
}

void
btor_insert_unsynthesized_constraint (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  BtorBitVector *bits;
  BtorPtrHashTable *uc;

  if (btor_is_bv_const_node (exp))
  {
    bits = btor_const_get_bits (exp);
    assert (bits->width == 1);
    if ((BTOR_IS_INVERTED_NODE (exp) && btor_get_bit_bv (bits, 0))
        || (!BTOR_IS_INVERTED_NODE (exp) && !btor_get_bit_bv (bits, 0)))
    {
      btor->inconsistent = true;
      return;
    }
    else
    {
      /* we do not add true */
      assert ((BTOR_IS_INVERTED_NODE (exp) && !btor_get_bit_bv (bits, 0))
              || (!BTOR_IS_INVERTED_NODE (exp) && btor_get_bit_bv (bits, 0)));
      return;
    }
  }

  uc = btor->unsynthesized_constraints;
  if (!btor_get_ptr_hash_table (uc, exp))
  {
    assert (!btor_get_ptr_hash_table (btor->embedded_constraints, exp));
    (void) btor_add_ptr_hash_table (uc, btor_copy_exp (btor, exp));
    BTOR_REAL_ADDR_NODE (exp)->constraint = 1;
    btor->stats.constraints.unsynthesized++;
  }
}

static void
insert_embedded_constraint (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);
  assert (!btor_is_bv_const_node (exp));

  if (!btor_get_ptr_hash_table (btor->embedded_constraints, exp))
  {
    assert (!btor_get_ptr_hash_table (btor->unsynthesized_constraints, exp));
    (void) btor_add_ptr_hash_table (btor->embedded_constraints,
                                    btor_copy_exp (btor, exp));
    BTOR_REAL_ADDR_NODE (exp)->constraint = 1;
    btor->stats.constraints.embedded++;
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
  bucket = btor_get_ptr_hash_table (vsc, left);

  if (!bucket)
  {
    BTORLOG (
        1, "add varsubst: %s -> %s", node2string (left), node2string (right));
    btor_add_ptr_hash_table (vsc, btor_copy_exp (btor, left))->data.as_ptr =
        btor_copy_exp (btor, right);
    /* do not set constraint flag, as they are gone after substitution
     * and treated differently */
    btor->stats.constraints.varsubst++;
  }
  /* if v = t_1 is already in varsubst, we
   * have to synthesize v = t_2 */
  else if (right != (BtorNode *) bucket->data.as_ptr)
  {
    eq = btor_eq_exp (btor, left, right);
    /* only add if it is not in a constraint table: can be already in
     * embedded or unsythesized constraints */
    if (!BTOR_REAL_ADDR_NODE (eq)->constraint)
      btor_insert_unsynthesized_constraint (btor, eq);
    btor_release_exp (btor, eq);
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
static int
occurrence_check (Btor *btor, BtorNode *left, BtorNode *right)
{
  assert (btor);
  assert (left);
  assert (right);

  BtorNode *cur, *real_left;
  BtorNodePtrQueue queue;
  int is_cyclic, i;
  BtorMemMgr *mm;
  BtorIntHashTable *cache;

  is_cyclic = 0;
  mm        = btor->mm;
  cache     = btor_new_int_hash_table (mm);
  real_left = BTOR_REAL_ADDR_NODE (left);
  BTOR_INIT_QUEUE (mm, queue);

  cur = BTOR_REAL_ADDR_NODE (right);
  goto OCCURRENCE_CHECK_ENTER_WITHOUT_POP;

  do
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_DEQUEUE (queue));
  OCCURRENCE_CHECK_ENTER_WITHOUT_POP:
    assert (!btor_is_proxy_node (cur));
    if (!btor_contains_int_hash_table (cache, cur->id))
    {
      btor_add_int_hash_table (cache, cur->id);
      if (cur == real_left)
      {
        is_cyclic = 1;
        break;
      }
      for (i = cur->arity - 1; i >= 0; i--) BTOR_ENQUEUE (queue, cur->e[i]);
    }
  } while (!BTOR_EMPTY_QUEUE (queue));
  BTOR_RELEASE_QUEUE (queue);
  btor_delete_int_hash_table (cache);
  return is_cyclic;
}

/* checks if we can substitute and normalizes arguments to substitution,
 * substitute left_result with right_result, exp is child of AND_NODE */
static int
normalize_substitution (Btor *btor,
                        BtorNode *exp,
                        BtorNode **left_result,
                        BtorNode **right_result)
{
  assert (btor_get_opt (btor, BTOR_OPT_VAR_SUBST));

  BtorNode *left, *right, *real_left, *real_right, *tmp, *inv, *var, *lambda;
  BtorNode *const_exp, *real_exp;
  int leadings;
  BtorBitVector *ic, *fc, *bits;
  BtorMemMgr *mm;
  BtorSubstCompKind comp;
  BtorSortId sort;

  assert (btor);
  assert (exp);
  assert (left_result);
  assert (right_result);
  assert (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 1);
  assert (btor_simplify_exp (btor, exp) == exp);

  mm = btor->mm;

  /* boolean BV_NODE, force assignment (right_result) w.r.t. phase */
  if (btor_is_bv_var_node (exp))
  {
    assert (btor_get_exp_width (btor, exp) == 1);
    sort = btor_bitvec_sort (btor, 1);
    if (BTOR_IS_INVERTED_NODE (exp))
    {
      *left_result  = btor_copy_exp (btor, BTOR_REAL_ADDR_NODE (exp));
      *right_result = btor_zero_exp (btor, sort);
    }
    else
    {
      *left_result  = btor_copy_exp (btor, exp);
      *right_result = btor_one_exp (btor, sort);
    }
    btor_release_sort (btor, sort);
    return 1;
  }

  if (btor_is_ult_node (exp)
      && (btor_is_bv_var_node (BTOR_REAL_ADDR_NODE (exp)->e[0])
          || btor_is_bv_var_node (BTOR_REAL_ADDR_NODE (exp)->e[1])))
  {
    real_exp = BTOR_REAL_ADDR_NODE (exp);

    if (BTOR_IS_INVERTED_NODE (exp))
      comp = BTOR_SUBST_COMP_UGTE_KIND;
    else
      comp = BTOR_SUBST_COMP_ULT_KIND;

    if (btor_is_bv_var_node (real_exp->e[0]))
    {
      var   = real_exp->e[0];
      right = real_exp->e[1];
    }
    else
    {
      assert (btor_is_bv_var_node (real_exp->e[1]));
      var   = real_exp->e[1];
      right = real_exp->e[0];
      comp  = reverse_subst_comp_kind (btor, comp);
    }

    /* ~a comp b is equal to a reverse_comp ~b,
     * where comp in ult, ulte, ugt, ugte
     * (e.g. reverse_comp of ult is ugt) */
    if (BTOR_IS_INVERTED_NODE (var))
    {
      var   = BTOR_REAL_ADDR_NODE (var);
      right = BTOR_INVERT_NODE (right);
      comp  = reverse_subst_comp_kind (btor, comp);
    }

    /* we do not create a lambda (index) if variable is already in
     * substitution table */
    assert (!BTOR_IS_INVERTED_NODE (var));
    if (btor_get_ptr_hash_table (btor->varsubst_constraints, var)) return 0;

    if (!btor_is_bv_const_node (right)) return 0;

    if (BTOR_IS_INVERTED_NODE (right))
      bits = btor_not_bv (mm, btor_const_get_bits (right));
    else
      bits = btor_copy_bv (mm, btor_const_get_bits (right));

    if (comp == BTOR_SUBST_COMP_ULT_KIND || comp == BTOR_SUBST_COMP_ULTE_KIND)
    {
      leadings = btor_get_num_leading_zeros_bv (bits);
      if (leadings > 0)
      {
        sort      = btor_bitvec_sort (btor, leadings);
        const_exp = btor_zero_exp (btor, sort);
        btor_release_sort (btor, sort);
        sort =
            btor_bitvec_sort (btor, btor_get_exp_width (btor, var) - leadings);
        lambda = btor_var_exp (btor, sort, 0);
        btor_release_sort (btor, sort);
        tmp = btor_concat_exp (btor, const_exp, lambda);
        insert_varsubst_constraint (btor, var, tmp);
        btor_release_exp (btor, const_exp);
        btor_release_exp (btor, lambda);
        btor_release_exp (btor, tmp);
      }
    }
    else
    {
      assert (comp == BTOR_SUBST_COMP_UGT_KIND
              || comp == BTOR_SUBST_COMP_UGTE_KIND);
      leadings = btor_get_num_leading_ones_bv (bits);
      if (leadings > 0)
      {
        sort      = btor_bitvec_sort (btor, leadings);
        const_exp = btor_ones_exp (btor, sort);
        btor_release_sort (btor, sort);
        sort =
            btor_bitvec_sort (btor, btor_get_exp_width (btor, var) - leadings);
        lambda = btor_var_exp (btor, sort, 0);
        btor_release_sort (btor, sort);
        tmp = btor_concat_exp (btor, const_exp, lambda);
        insert_varsubst_constraint (btor, var, tmp);
        btor_release_exp (btor, const_exp);
        btor_release_exp (btor, lambda);
        btor_release_exp (btor, tmp);
      }
    }

    btor_free_bv (btor->mm, bits);
    return 0;
  }

  /* in the boolean case a != b is the same as a == ~b */
  if (BTOR_IS_INVERTED_NODE (exp) && btor_is_bv_eq_node (exp)
      && btor_get_exp_width (btor, BTOR_REAL_ADDR_NODE (exp)->e[0]) == 1)
  {
    left  = BTOR_REAL_ADDR_NODE (exp)->e[0];
    right = BTOR_REAL_ADDR_NODE (exp)->e[1];

    if (btor_is_bv_var_node (left))
    {
      *left_result  = btor_copy_exp (btor, left);
      *right_result = BTOR_INVERT_NODE (btor_copy_exp (btor, right));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }

    if (btor_is_bv_var_node (right))
    {
      *left_result  = btor_copy_exp (btor, right);
      *right_result = BTOR_INVERT_NODE (btor_copy_exp (btor, left));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }
  }

  if (BTOR_IS_INVERTED_NODE (exp) || !btor_is_array_or_bv_eq_node (exp))
    return 0;

  left       = exp->e[0];
  right      = exp->e[1];
  real_left  = BTOR_REAL_ADDR_NODE (left);
  real_right = BTOR_REAL_ADDR_NODE (right);

  if (!btor_is_bv_var_node (real_left) && !btor_is_bv_var_node (real_right)
      && !btor_is_uf_node (real_left) && !btor_is_uf_node (real_right))
  {
    if (btor_rewrite_linear_term (btor, left, &fc, left_result, &tmp))
      *right_result = btor_sub_exp (btor, right, tmp);
    else if (btor_rewrite_linear_term (btor, right, &fc, left_result, &tmp))
      *right_result = btor_sub_exp (btor, left, tmp);
    else
      return 0;

    btor->stats.gaussian_eliminations++;

    btor_release_exp (btor, tmp);
    ic = btor_mod_inverse_bv (btor->mm, fc);
    btor_free_bv (btor->mm, fc);
    inv = btor_const_exp (btor, ic);
    btor_free_bv (btor->mm, ic);
    tmp = btor_mul_exp (btor, *right_result, inv);
    btor_release_exp (btor, inv);
    btor_release_exp (btor, *right_result);
    *right_result = tmp;
  }
  else
  {
    if ((!btor_is_bv_var_node (real_left) && btor_is_bv_var_node (real_right))
        || (!btor_is_uf_node (real_left) && btor_is_uf_node (real_right)))
    {
      *left_result  = right;
      *right_result = left;
    }
    else
    {
      *left_result  = left;
      *right_result = right;
    }

    btor_copy_exp (btor, left);
    btor_copy_exp (btor, right);
  }

BTOR_NORMALIZE_SUBST_RESULT:
  if (BTOR_IS_INVERTED_NODE (*left_result))
  {
    *left_result  = BTOR_INVERT_NODE (*left_result);
    *right_result = BTOR_INVERT_NODE (*right_result);
  }

  if (occurrence_check (btor, *left_result, *right_result))
  {
    btor_release_exp (btor, *left_result);
    btor_release_exp (btor, *right_result);
    return 0;
  }

  return 1;
}

static int
constraint_is_inconsistent (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  //  assert (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 1);
  assert (btor_get_exp_width (btor, exp) == 1);

  BtorNode *rep;

  rep = btor_simplify_exp (btor, exp);

  return rep == BTOR_INVERT_NODE (rep)
         /* special case: top-level constraint applies are not simplified to
          * true/false (in order to not break dual prop) */
         || btor_get_ptr_hash_table (btor->synthesized_constraints,
                                     BTOR_INVERT_NODE (rep))
         || btor_get_ptr_hash_table (btor->unsynthesized_constraints,
                                     BTOR_INVERT_NODE (rep))
         || btor_get_ptr_hash_table (btor->embedded_constraints,
                                     BTOR_INVERT_NODE (rep));
}

static int
is_embedded_constraint_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return btor_get_exp_width (btor, exp) == 1
         && BTOR_REAL_ADDR_NODE (exp)->parents > 0;
}

static void
insert_new_constraint (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_get_exp_width (btor, exp) == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  BtorBitVector *bits;
  BtorNode *left, *right, *real_exp;

  exp      = btor_simplify_exp (btor, exp);
  real_exp = BTOR_REAL_ADDR_NODE (exp);

  if (btor_is_bv_const_node (real_exp))
  {
    bits = btor_const_get_bits (real_exp);
    assert (bits->width == 1);
    /* we do not add true/false */
    if ((BTOR_IS_INVERTED_NODE (exp) && btor_get_bit_bv (bits, 0))
        || (!BTOR_IS_INVERTED_NODE (exp) && !btor_get_bit_bv (bits, 0)))
      btor->inconsistent = true;
    else
    {
      assert ((BTOR_IS_INVERTED_NODE (exp) && !btor_get_bit_bv (bits, 0))
              || (!BTOR_IS_INVERTED_NODE (exp) && btor_get_bit_bv (bits, 0)));
    }
    return;
  }

  if (!btor_get_ptr_hash_table (btor->synthesized_constraints, exp))
  {
    if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 1)
    {
      if (btor_get_opt (btor, BTOR_OPT_VAR_SUBST)
          && normalize_substitution (btor, exp, &left, &right))
      {
        insert_varsubst_constraint (btor, left, right);
        btor_release_exp (btor, left);
        btor_release_exp (btor, right);
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
      if (constraint_is_inconsistent (btor, exp))
        btor->inconsistent = true;
      else
      {
        if (!real_exp->constraint)
        {
          if (is_embedded_constraint_exp (btor, exp))
            insert_embedded_constraint (btor, exp);
          else
            btor_insert_unsynthesized_constraint (btor, exp);
        }
        else
        {
          assert (btor_get_ptr_hash_table (btor->unsynthesized_constraints, exp)
                  || btor_get_ptr_hash_table (btor->embedded_constraints, exp));
        }
      }
    }
    else if (constraint_is_inconsistent (btor, exp))
      btor->inconsistent = true;
    else
      btor_insert_unsynthesized_constraint (btor, exp);

    report_constraint_stats (btor, 0);
  }
}

void
btor_reset_assumptions (Btor *btor)
{
  assert (btor);

  BtorPtrHashTableIterator it;

  btor_init_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_ptr_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (btor->assumptions);
  btor->assumptions =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
reset_functions_with_model (Btor *btor)
{
  BtorNode *cur;
  int i;

  assert (btor);

  for (i = 0; i < BTOR_COUNT_STACK (btor->functions_with_model); i++)
  {
    cur = btor->functions_with_model.start[i];
    assert (!BTOR_IS_INVERTED_NODE (cur));
    if (!btor_is_proxy_node (cur))
    {
      assert (btor_is_fun_node (cur));
      assert (cur->rho);
      btor_delete_ptr_hash_table (cur->rho);
      cur->rho = 0;
    }
    btor_release_exp (btor, cur);
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
  btor_delete_model (btor);
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
  assert (!btor_is_fun_node (exp));
  assert (btor_get_exp_width (btor, exp) == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);
  mm   = btor->mm;
  mark = btor_new_int_hash_table (mm);

  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!BTOR_IS_INVERTED_NODE (exp) && btor_is_and_node (exp))
  {
    BTOR_INIT_STACK (mm, stack);
    cur = exp;
    goto ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP:
      assert (!BTOR_IS_INVERTED_NODE (cur));
      assert (btor_is_and_node (cur));
      if (!btor_contains_int_hash_table (mark, cur->id))
      {
        btor_add_int_hash_table (mark, cur->id);
        child = cur->e[1];
        if (!BTOR_IS_INVERTED_NODE (child) && btor_is_and_node (child))
          BTOR_PUSH_STACK (stack, child);
        else
          insert_new_constraint (btor, child);
        child = cur->e[0];
        if (!BTOR_IS_INVERTED_NODE (child) && btor_is_and_node (child))
          BTOR_PUSH_STACK (stack, child);
        else
          insert_new_constraint (btor, child);
      }
    } while (!BTOR_EMPTY_STACK (stack));
    BTOR_RELEASE_STACK (stack);
  }
  else
    insert_new_constraint (btor, exp);

  btor_delete_int_hash_table (mark);
  assert (btor_check_constraints_not_const_dbg (btor));
}

void
btor_assert_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!btor_is_fun_node (exp));
  assert (btor_get_exp_width (btor, exp) == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  add_constraint (btor, exp);
}

static int
exp_to_cnf_lit (Btor *btor, BtorNode *exp)
{
  int res, sign, val;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorAIG *aig;

  assert (btor);
  assert (exp);
  assert (btor_get_exp_width (btor, exp) == 1);

  exp = btor_simplify_exp (btor, exp);

  sign = 1;

  if (BTOR_IS_INVERTED_NODE (exp))
  {
    exp = BTOR_INVERT_NODE (exp);
    sign *= -1;
  }

  aig = exp_to_aig (btor, exp);

  amgr = btor_get_aig_mgr_btor (btor);
  smgr = btor_get_sat_mgr_btor (btor);

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
    btor_release_aig (amgr, aig);

    if ((val = btor_fixed_sat (smgr, res)))
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
  assert (btor_get_opt (btor, BTOR_OPT_INCREMENTAL));
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  /* Note: do not simplify constraint expression in order to prevent
   *       constraint expressions from not being added to btor->assumptions. */
  exp = btor_pointer_chase_simplified_exp (btor, exp);

  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!btor_get_ptr_hash_table (btor->assumptions, exp))
    (void) btor_add_ptr_hash_table (btor->assumptions,
                                    btor_copy_exp (btor, exp));
}

bool
btor_is_assumption_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor_get_opt (btor, BTOR_OPT_INCREMENTAL));
  assert (exp);

  /* Note: do not simplify constraint expression in order to prevent
   *       constraint expressions from not being added to btor->assumptions. */
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return btor_get_ptr_hash_table (btor->assumptions, exp) ? true : false;
}

bool
btor_failed_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor_get_opt (btor, BTOR_OPT_INCREMENTAL));
  assert (btor->last_sat_result == BTOR_RESULT_UNSAT);
  assert (exp);
  assert (btor_is_assumption_exp (btor, exp));

  bool res;
  int i, lit;
  double start;
  BtorAIG *aig;
  BtorNode *real_exp, *cur, *e;
  BtorNodePtrStack work_stack, assumptions;
  BtorSATMgr *smgr;
  BtorIntHashTable *mark;

  start = btor_time_stamp ();

  /* Note: do not simplify constraint expression in order to prevent
   *       constraint expressions from not being added to btor->assumptions. */
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->btor == btor);
  assert (!btor_is_fun_node (exp));
  assert (btor_get_exp_width (btor, exp) == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);
  assert (btor_is_assumption_exp (btor, exp));
  mark = btor_new_int_hash_table (btor->mm);
  smgr = btor_get_sat_mgr_btor (btor);
  assert (smgr);

  if (btor->inconsistent)
  {
    res = false;
  }
  else if (exp == btor->true_exp)
  {
    res = false;
  }
  else if (exp == BTOR_INVERT_NODE (btor->true_exp))
  {
    res = true;
  }
  else if (!btor_is_initialized_sat (smgr))
  {
    res = true;
  }
  else if (BTOR_IS_INVERTED_NODE (exp) || !btor_is_and_node (exp))
  {
    real_exp = BTOR_REAL_ADDR_NODE (exp);
    assert (btor->found_constraint_false || BTOR_IS_SYNTH_NODE (real_exp));

    if (!BTOR_IS_SYNTH_NODE (real_exp))
    {
      res = false;
    }
    else if (btor->found_constraint_false)
    {
      res = ((BTOR_IS_INVERTED_NODE (exp)
              && real_exp->av->aigs[0] == BTOR_AIG_TRUE)
             || (!BTOR_IS_INVERTED_NODE (exp)
                 && real_exp->av->aigs[0] == BTOR_AIG_FALSE));
    }
    else
    {
      if ((BTOR_IS_INVERTED_NODE (exp)
           && real_exp->av->aigs[0] == BTOR_AIG_FALSE)
          || (!BTOR_IS_INVERTED_NODE (exp)
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
          res = btor_failed_sat (smgr, lit) > 0;
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
      assert (!BTOR_IS_INVERTED_NODE (cur));
      assert (btor_is_and_node (cur));
      if (btor_contains_int_hash_table (mark, cur->id)) continue;
      btor_add_int_hash_table (mark, cur->id);
      for (i = 0; i < 2; i++)
      {
        e = cur->e[i];
        if (!BTOR_IS_INVERTED_NODE (e) && btor_is_and_node (e))
          BTOR_PUSH_STACK (work_stack, e);
        else
        {
          if (!BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (e))) continue;

          aig = BTOR_REAL_ADDR_NODE (e)->av->aigs[0];
          if ((BTOR_IS_INVERTED_NODE (e) && aig == BTOR_AIG_FALSE)
              || (!BTOR_IS_INVERTED_NODE (e) && aig == BTOR_AIG_TRUE))
            continue;
          if ((BTOR_IS_INVERTED_NODE (e) && aig == BTOR_AIG_TRUE)
              || (!BTOR_IS_INVERTED_NODE (e) && aig == BTOR_AIG_FALSE))
            goto ASSUMPTION_FAILED;
          if (btor->found_constraint_false) continue;
          BTOR_PUSH_STACK (assumptions, e);
        }
      }
    }

    while (!BTOR_EMPTY_STACK (assumptions))
    {
      cur = BTOR_POP_STACK (assumptions);
      assert (BTOR_IS_INVERTED_NODE (cur) || !btor_is_and_node (cur));
      lit = exp_to_cnf_lit (btor, cur);
      if (lit == smgr->true_lit) continue;
      if (lit == -smgr->true_lit) goto ASSUMPTION_FAILED;
      if (btor_failed_sat (smgr, lit))
      {
      ASSUMPTION_FAILED:
        BTOR_RELEASE_STACK (work_stack);
        BTOR_RELEASE_STACK (assumptions);
        res = true;
      }
    }
    BTOR_RELEASE_STACK (work_stack);
    BTOR_RELEASE_STACK (assumptions);
  }

  btor_delete_int_hash_table (mark);
  btor->time.failed += btor_time_stamp () - start;

  return res;
}

void
btor_fixate_assumptions (Btor *btor)
{
  BtorPtrHashTableIterator it;
  btor_init_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    btor_assert_exp (btor, btor_next_ptr_hash_table_iterator (&it));
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
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (exp->simplified);
  assert (!BTOR_REAL_ADDR_NODE (exp->simplified)->simplified);
  assert (exp->constraint);
  assert (exp->refs > 1);
  assert (!exp->parameterized);
  assert (!BTOR_REAL_ADDR_NODE (exp->simplified)->parameterized);

  not_exp                   = BTOR_INVERT_NODE (exp);
  simplified                = exp->simplified;
  not_simplified            = BTOR_INVERT_NODE (simplified);
  embedded_constraints      = btor->embedded_constraints;
  unsynthesized_constraints = btor->unsynthesized_constraints;
  synthesized_constraints   = btor->synthesized_constraints;
  pos = neg = 0;

  if (btor_get_ptr_hash_table (unsynthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = unsynthesized_constraints;
  }

  if (btor_get_ptr_hash_table (unsynthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = unsynthesized_constraints;
  }

  if (btor_get_ptr_hash_table (embedded_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = embedded_constraints;
  }

  if (btor_get_ptr_hash_table (embedded_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = embedded_constraints;
  }

  if (btor_get_ptr_hash_table (synthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = synthesized_constraints;
  }

  if (btor_get_ptr_hash_table (synthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = synthesized_constraints;
  }

  if (pos)
  {
    btor_remove_ptr_hash_table (pos, exp, 0, 0);
    btor_release_exp (btor, exp);
  }

  if (neg)
  {
    btor_remove_ptr_hash_table (neg, not_exp, 0, 0);
    btor_release_exp (btor, not_exp);
  }

  exp->constraint = 0;
}

static void
set_simplified_exp (Btor *btor, BtorNode *exp, BtorNode *simplified)
{
  assert (btor);
  assert (exp);
  assert (simplified);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!BTOR_REAL_ADDR_NODE (simplified)->simplified);
  assert (exp->arity <= 3);
  assert (btor_exp_get_sort_id (exp) == btor_exp_get_sort_id (simplified));
  assert (exp->parameterized
          || !BTOR_REAL_ADDR_NODE (simplified)->parameterized);
  assert (!BTOR_REAL_ADDR_NODE (simplified)->parameterized
          || exp->parameterized);

  if (exp->simplified) btor_release_exp (btor, exp->simplified);

  exp->simplified = btor_copy_exp (btor, simplified);

  if (exp->constraint) update_constraints (btor, exp);

  /* if a variable or UF gets simplified we need to save the original input
   * exp in a hash table (for model generation) */
  if (btor_is_bv_var_node (exp)
      && !btor_get_ptr_hash_table (btor->var_rhs, exp))
  {
    btor_add_ptr_hash_table (btor->var_rhs, btor_copy_exp (btor, exp));
  }
  else if (btor_is_uf_node (exp)
           && !btor_get_ptr_hash_table (btor->fun_rhs, exp))
  {
    btor_add_ptr_hash_table (btor->fun_rhs, btor_copy_exp (btor, exp));
  }

  btor_set_to_proxy_exp (btor, exp);

  /* if simplified is parameterized, exp was also parameterized */
  if (BTOR_REAL_ADDR_NODE (simplified)->parameterized) exp->parameterized = 1;
}

/* Finds most simplified expression and shortens path to it */
static BtorNode *
recursively_pointer_chase_simplified_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp, *cur, *simplified, *not_simplified, *next;
  int invert;

  assert (btor);
  assert (exp);

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  assert (real_exp->simplified);
  assert (BTOR_REAL_ADDR_NODE (real_exp->simplified)->simplified);

  /* shorten path to simplified expression */
  invert     = 0;
  simplified = real_exp->simplified;
  do
  {
    assert (btor_is_proxy_node (simplified));
    if (BTOR_IS_INVERTED_NODE (simplified)) invert = !invert;
    simplified = BTOR_REAL_ADDR_NODE (simplified)->simplified;
  } while (BTOR_REAL_ADDR_NODE (simplified)->simplified);
  /* 'simplified' is representative element */
  assert (!BTOR_REAL_ADDR_NODE (simplified)->simplified);
  if (invert) simplified = BTOR_INVERT_NODE (simplified);

  invert         = 0;
  not_simplified = BTOR_INVERT_NODE (simplified);
  cur            = btor_copy_exp (btor, real_exp);
  do
  {
    if (BTOR_IS_INVERTED_NODE (cur)) invert = !invert;
    cur  = BTOR_REAL_ADDR_NODE (cur);
    next = btor_copy_exp (btor, cur->simplified);
    set_simplified_exp (btor, cur, invert ? not_simplified : simplified);
    btor_release_exp (btor, cur);
    cur = next;
  } while (BTOR_REAL_ADDR_NODE (cur)->simplified);
  btor_release_exp (btor, cur);

  /* if starting expression is inverted, then we have to invert result */
  if (BTOR_IS_INVERTED_NODE (exp)) simplified = BTOR_INVERT_NODE (simplified);

  return simplified;
}

BtorNode *
btor_pointer_chase_simplified_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp;

  assert (btor);
  assert (exp);
  (void) btor;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  /* no simplified expression ? */
  if (!real_exp->simplified) return exp;

  /* only one simplified expression ? */
  if (!BTOR_REAL_ADDR_NODE (real_exp->simplified)->simplified)
  {
    if (BTOR_IS_INVERTED_NODE (exp))
      return BTOR_INVERT_NODE (real_exp->simplified);
    return exp->simplified;
  }
  return recursively_pointer_chase_simplified_exp (btor, exp);
}

static BtorNode *
simplify_constraint_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->constraint);
  assert (!BTOR_REAL_ADDR_NODE (exp)->simplified);
  /* embedded constraints rewriting enabled with rwl > 1 */
  assert (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 1);

  BtorNode *real_exp, *result, *not_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  /* Do not simplify top-level constraint applies (we need the implication
   * dependencies for determining top applies when dual prop enabled) */
  if (btor_get_opt (btor, BTOR_OPT_FUN_DUAL_PROP)
      && btor_is_apply_node (real_exp))
    return exp;

  not_exp = BTOR_INVERT_NODE (real_exp);

  if (btor_is_bv_const_node (real_exp)) return exp;

  if (btor_get_ptr_hash_table (btor->embedded_constraints, real_exp))
  {
    result = btor->true_exp;
  }
  else if (btor_get_ptr_hash_table (btor->embedded_constraints, not_exp))
  {
    result = BTOR_INVERT_NODE (btor->true_exp);
  }
  else if (btor_get_ptr_hash_table (btor->unsynthesized_constraints, real_exp))
  {
    result = btor->true_exp;
  }
  else if (btor_get_ptr_hash_table (btor->unsynthesized_constraints, not_exp))
  {
    result = BTOR_INVERT_NODE (btor->true_exp);
  }
  else if (btor_get_ptr_hash_table (btor->synthesized_constraints, real_exp))
  {
    result = btor->true_exp;
  }
  else
  {
    assert (btor_get_ptr_hash_table (btor->synthesized_constraints, not_exp));
    result = BTOR_INVERT_NODE (btor->true_exp);
  }

  if (BTOR_IS_INVERTED_NODE (exp)) return BTOR_INVERT_NODE (result);

  return result;
}

BtorNode *
btor_simplify_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (exp)->refs > 0);

  BtorNode *result;

  result = btor_pointer_chase_simplified_exp (btor, exp);

  /* NOTE: embedded constraints rewriting is enabled with rwl > 1 */
  if (btor_get_opt (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS)
      && btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 1
      && BTOR_REAL_ADDR_NODE (result)->constraint)
    return simplify_constraint_exp (btor, result);

  assert (BTOR_REAL_ADDR_NODE (result)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (result)->refs > 0);

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
  btor_init_ptr_hash_table_iterator (&it, btor->lambdas);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur        = btor_next_ptr_hash_table_iterator (&it);
    static_rho = btor_lambda_get_static_rho (cur);

    if (!static_rho) continue;

    new_static_rho =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    /* update static rho to get rid of proxy nodes */
    btor_init_ptr_hash_table_iterator (&iit, static_rho);
    while (btor_has_next_ptr_hash_table_iterator (&iit))
    {
      data = iit.bucket->data.as_ptr;
      key  = btor_next_ptr_hash_table_iterator (&iit);
      assert (BTOR_IS_REGULAR_NODE (key));
      simp_key  = btor_simplify_exp (btor, key);
      simp_data = btor_simplify_exp (btor, data);

      if (!btor_get_ptr_hash_table (new_static_rho, simp_key))
      {
        btor_add_ptr_hash_table (new_static_rho, btor_copy_exp (btor, simp_key))
            ->data.as_ptr = btor_copy_exp (btor, simp_data);
      }
      btor_release_exp (btor, key);
      btor_release_exp (btor, data);
    }
    btor_delete_ptr_hash_table (static_rho);
    btor_lambda_set_static_rho (cur, new_static_rho);
  }
}

static BtorNode *
rebuild_lambda_exp (Btor *btor, BtorNode *exp)
{
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_lambda_node (exp));
  assert (!btor_param_get_assigned_exp (exp->e[0]));

  BtorNode *result;

  /* we need to reset the binding lambda here as otherwise it is not possible
   * to create a new lambda term with the same param that substitutes 'exp' */
  btor_param_set_binding_lambda (exp->e[0], 0);
  result = btor_lambda_exp (btor, exp->e[0], exp->e[1]);

  /* lambda not rebuilt, set binding lambda again */
  if (result == exp) btor_param_set_binding_lambda (exp->e[0], exp);

  /* copy static_rho for new lambda */
  if (btor_lambda_get_static_rho (exp) && !btor_lambda_get_static_rho (result))
    btor_lambda_set_static_rho (result,
                                btor_lambda_copy_static_rho (btor, exp));
  if (exp->is_array) result->is_array = 1;
  return result;
}

static BtorNode *
rebuild_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  switch (exp->kind)
  {
    case BTOR_PROXY_NODE:
    case BTOR_BV_CONST_NODE:
    case BTOR_BV_VAR_NODE:
    case BTOR_PARAM_NODE:
    case BTOR_UF_NODE:
      return btor_copy_exp (btor, btor_simplify_exp (btor, exp));
    case BTOR_SLICE_NODE:
      return btor_slice_exp (btor,
                             exp->e[0],
                             btor_slice_get_upper (exp),
                             btor_slice_get_lower (exp));
    case BTOR_LAMBDA_NODE: return rebuild_lambda_exp (btor, exp);
    default: return btor_create_exp (btor, exp->kind, exp->e, exp->arity);
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
  int pushed, i;

  if (substs->count == 0u) return;

  mm   = btor->mm;
  mark = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, root_stack);
  /* search upwards for all reachable roots */
  /* we push all left sides on the search stack */
  btor_init_ptr_hash_table_iterator (&it, substs);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (btor_is_bv_var_node (cur) || btor_is_uf_node (cur));
    BTOR_PUSH_STACK (stack, cur);
  }

  do
  {
    assert (!BTOR_EMPTY_STACK (stack));
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (!btor_contains_int_hash_map (mark, cur->id))
    {
      btor_add_int_hash_map (mark, cur->id);
      btor_init_parent_iterator (&nit, cur);
      /* are we at a root ? */
      pushed = 0;
      while (btor_has_next_parent_iterator (&nit))
      {
        cur_parent = btor_next_parent_iterator (&nit);
        assert (BTOR_IS_REGULAR_NODE (cur_parent));
        pushed = 1;
        BTOR_PUSH_STACK (stack, cur_parent);
      }
      if (!pushed) BTOR_PUSH_STACK (root_stack, btor_copy_exp (btor, cur));
    }
  } while (!BTOR_EMPTY_STACK (stack));

  /* copy roots on substitution stack */
  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    BTOR_PUSH_STACK (stack, *temp);

  /* substitute */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

    d = btor_get_int_hash_map (mark, cur->id);
    if (!d) continue;

    assert (!btor_is_bv_const_node (cur));

    if (d->as_int == 0)
    {
      BTOR_PUSH_STACK (stack, cur);
      d->as_int = 1;
      if (btor_is_bv_var_node (cur) || btor_is_uf_node (cur))
      {
        b = btor_get_ptr_hash_table (substs, cur);
        assert (b);
        assert (cur == (BtorNode *) b->key);
        rhs = (BtorNode *) b->data.as_ptr;
        assert (rhs);
        BTOR_PUSH_STACK (stack, rhs);
      }
      else
      {
        for (i = cur->arity - 1; i >= 0; i--)
          BTOR_PUSH_STACK (stack, cur->e[i]);
      }
    }
    else
    {
      assert (d->as_int == 1);
      btor_remove_int_hash_map (mark, cur->id, 0);
      if (btor_is_bv_var_node (cur) || btor_is_uf_node (cur))
      {
        b = btor_get_ptr_hash_table (substs, cur);
        assert (b);
        assert (cur == (BtorNode *) b->key);
        rhs = (BtorNode *) b->data.as_ptr;
        assert (rhs);
        rebuilt_exp = btor_copy_exp (btor, rhs);
        if (btor_is_bv_var_node (cur))
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
      btor_release_exp (btor, rebuilt_exp);
    }
  }

  BTOR_RELEASE_STACK (stack);

  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    btor_release_exp (btor, *temp);
  BTOR_RELEASE_STACK (root_stack);

  update_node_hash_tables (btor);
  btor_delete_int_hash_map (mark);
  assert (btor_check_lambdas_static_rho_proxy_free_dbg (btor));
}

static void
substitute_var_exps (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *varsubst_constraints, *order, *substs;
  BtorNode *cur, *constraint, *left, *right, *child;
  BtorPtrHashBucket *b, *b_temp;
  BtorPtrHashTableIterator it;
  int order_num, val, max, i;
  BtorNodePtrStack stack;
  double start, delta;
  unsigned count;
  BtorMemMgr *mm;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  mm                   = btor->mm;
  varsubst_constraints = btor->varsubst_constraints;

  if (varsubst_constraints->count == 0u) return;

  start = btor_time_stamp ();

  BTOR_INIT_STACK (mm, stack);

  /* new equality constraints may be added during rebuild */
  count = 0;
  while (varsubst_constraints->count > 0u)
  {
    order_num = 1;
    order     = btor_new_ptr_hash_table (mm,
                                     (BtorHashPtr) btor_hash_exp_by_id,
                                     (BtorCmpPtr) btor_compare_exp_by_id);

    substs = btor_new_ptr_hash_table (mm,
                                      (BtorHashPtr) btor_hash_exp_by_id,
                                      (BtorCmpPtr) btor_compare_exp_by_id);

    /* we copy the current substitution constraints into a local hash table,
     * and empty the global substitution table */
    while (varsubst_constraints->count > 0u)
    {
      count++;
      b   = varsubst_constraints->first;
      cur = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (btor_is_bv_var_node (cur) || btor_is_uf_node (cur));
      right = (BtorNode *) b->data.as_ptr;
      /* NOTE: we need to update 'right' here, since 'right' might have
       * already been rebuilt in merge_lambdas (in beta reduction part) */
      btor_add_ptr_hash_table (substs, cur)->data.as_ptr =
          btor_copy_exp (btor, btor_simplify_exp (btor, right));
      btor_release_exp (btor, right);
      btor_remove_ptr_hash_table (varsubst_constraints, cur, 0, 0);
    }
    assert (varsubst_constraints->count == 0u);

    mark = btor_new_int_hash_table (mm);
    /* we search for cyclic substitution dependencies
     * and map the substitutions to an ordering number */
    btor_init_ptr_hash_table_iterator (&it, substs);
    while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      cur = btor_next_ptr_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (btor_is_bv_var_node (cur) || btor_is_uf_node (cur));
      BTOR_PUSH_STACK (stack, cur);

      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

        if (!cur)
        {
          cur = BTOR_POP_STACK (stack); /* left */
          assert (BTOR_IS_REGULAR_NODE (cur));
          assert (btor_is_bv_var_node (cur) || btor_is_uf_node (cur));
          assert (!btor_get_ptr_hash_table (order, cur));
          btor_add_ptr_hash_table (order, cur)->data.as_int = order_num++;
          continue;
        }
        /* visited (DFS) */
        if (btor_contains_int_hash_table (mark, cur->id)) continue;

        btor_add_int_hash_table (mark, cur->id);

        if (btor_is_bv_const_node (cur) || btor_is_bv_var_node (cur)
            || btor_is_param_node (cur) || btor_is_uf_node (cur))
        {
          b_temp = btor_get_ptr_hash_table (substs, cur);
          if (b_temp)
          {
            BTOR_PUSH_STACK (stack, cur); /* left  */
            BTOR_PUSH_STACK (stack, 0);
            BTOR_PUSH_STACK (stack, /* right */
                             (BtorNode *) b_temp->data.as_ptr);
          }
          else
          {
            assert (!btor_get_ptr_hash_table (order, cur));
            btor_add_ptr_hash_table (order, cur)->data.as_int = 0;
          }
        }
        else
        {
          assert (cur->arity >= 1);
          assert (cur->arity <= 3);
          for (i = cur->arity - 1; i >= 0; i--)
            BTOR_PUSH_STACK (stack, cur->e[i]);
        }
      }
    }

    btor_delete_int_hash_table (mark);
    mark = btor_new_int_hash_map (mm);

    /* we look for cycles */
    btor_init_ptr_hash_table_iterator (&it, substs);
    while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      b   = it.bucket;
      cur = btor_next_ptr_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (btor_is_bv_var_node (cur) || btor_is_uf_node (cur));
      BTOR_PUSH_STACK (stack, (BtorNode *) b->data.as_ptr);

      /* we assume that there are no direct loops
       * as a result of occurrence check */
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
        d   = btor_get_int_hash_map (mark, cur->id);

        if (d && d->as_int == 1) /* cur has max order of its children */
          continue;

        if (btor_is_bv_const_node (cur) || btor_is_bv_var_node (cur)
            || btor_is_param_node (cur) || btor_is_uf_node (cur))
        {
          assert (btor_get_ptr_hash_table (order, cur));
          continue;
        }

        assert (cur->arity >= 1);
        assert (cur->arity <= 3);

        if (!d)
        {
          btor_add_int_hash_map (mark, cur->id);
          BTOR_PUSH_STACK (stack, cur);
          for (i = cur->arity - 1; i >= 0; i--)
            BTOR_PUSH_STACK (stack, cur->e[i]);
        }
        else /* cur is visited, its children are visited */
        {
          /* compute maximum of children */
          assert (d->as_int == 0);
          d->as_int = 1;
          max       = 0;
          for (i = cur->arity - 1; i >= 0; i--)
          {
            child  = BTOR_REAL_ADDR_NODE (cur->e[i]);
            b_temp = btor_get_ptr_hash_table (order, child);
            assert (b_temp);
            val = b_temp->data.as_int;
            assert (val >= 0);
            max = BTOR_MAX_UTIL (max, val);
          }
          btor_add_ptr_hash_table (order, cur)->data.as_int = max;
        }
      }
    }
    btor_delete_int_hash_map (mark);

    assert (BTOR_EMPTY_STACK (stack));
    /* we eliminate cyclic substitutions, and reset mark flags */
    btor_init_ptr_hash_table_iterator (&it, substs);
    while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      right = (BtorNode *) it.bucket->data.as_ptr;
      assert (right);
      left = btor_next_ptr_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (btor_is_bv_var_node (left) || btor_is_uf_node (left));
      b_temp = btor_get_ptr_hash_table (order, left);
      assert (b_temp);
      order_num = b_temp->data.as_int;
      b_temp    = btor_get_ptr_hash_table (order, BTOR_REAL_ADDR_NODE (right));
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
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (btor_is_bv_var_node (left) || btor_is_uf_node (left));
      right = (BtorNode *) btor_get_ptr_hash_table (substs, left)->data.as_ptr;
      assert (right);

      constraint = btor_eq_exp (btor, left, right);
      /* only add if it is not in a constraint table: can be already in
       * embedded or unsythesized constraints */
      if (!BTOR_REAL_ADDR_NODE (constraint)->constraint)
        btor_insert_unsynthesized_constraint (btor, constraint);
      btor_release_exp (btor, constraint);

      btor_remove_ptr_hash_table (substs, left, 0, 0);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    /* we rebuild and substiute variables in one pass */
    substitute_vars_and_rebuild_exps (btor, substs);

    /* cleanup, we delete all substitution constraints */
    btor_init_ptr_hash_table_iterator (&it, substs);
    while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      right = (BtorNode *) it.bucket->data.as_ptr;
      assert (right);
      left = btor_next_ptr_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (btor_is_proxy_node (left));
      assert (left->simplified);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    btor_delete_ptr_hash_table (order);
    btor_delete_ptr_hash_table (substs);
  }

  BTOR_RELEASE_STACK (stack);
  delta = btor_time_stamp () - start;
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

  int i;
  BtorNode *cur;

  cur = btor_find_substitution (btor, exp);
  if (cur)
  {
    cur = btor_simplify_exp (btor, cur);
    return !btor_contains_int_hash_map (mark, BTOR_REAL_ADDR_NODE (cur)->id);
  }

  exp = BTOR_REAL_ADDR_NODE (exp);
  for (i = 0; i < exp->arity; i++)
  {
    cur = BTOR_REAL_ADDR_NODE (btor_simplify_exp (btor, exp->e[i]));
    if (btor_contains_int_hash_map (mark, cur->id)) return false;
  }

  return true;
}

BtorNode *
btor_substitute_terms (Btor *btor, BtorNode *root, BtorNodeMap *substs)
{
  assert (btor);
  assert (root);
  assert (substs);

  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *subst, *result, **e;
  BtorNodePtrStack visit, args, cleanup;
  BtorIntHashTable *mark, *cache;
  BtorHashTableData *d;

  mm    = btor->mm;
  mark  = btor_new_int_hash_map (mm);
  cache = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, cleanup);
  BTOR_PUSH_STACK (visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    subst    = btor_mapped_node (substs, real_cur);
    // TODO (ma): for now we only support bit vector terms
    assert (!btor_is_lambda_node (real_cur));

    if (subst)
    {
      result = btor_copy_exp (btor, subst);
      goto PUSH_RESULT;
    }

    d = btor_get_int_hash_map (mark, real_cur->id);
    if (!d)
    {
      (void) btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;

      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        result = btor_copy_exp (btor, real_cur);
      }
      else if (real_cur->arity == 1)
      {
        assert (btor_is_slice_node (real_cur));
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      else
      {
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);
      }
      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);
      assert (!btor_get_int_hash_map (cache, real_cur->id));
      btor_add_int_hash_map (cache, real_cur->id)->as_ptr =
          btor_copy_exp (btor, result);
      BTOR_PUSH_STACK (cleanup, result);
    PUSH_RESULT:
      BTOR_PUSH_STACK (args, BTOR_COND_INVERT_NODE (cur, result));
    }
    else
    {
      assert (d->as_int == 1);
      d = btor_get_int_hash_map (cache, real_cur->id);
      assert (d);
      result = btor_copy_exp (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  while (!BTOR_EMPTY_STACK (cleanup))
    btor_release_exp (btor, BTOR_POP_STACK (cleanup));
  BTOR_RELEASE_STACK (cleanup);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);
  btor_delete_int_hash_map (cache);
  btor_delete_int_hash_map (mark);
  return result;
}

static void
substitute_and_rebuild (Btor *btor, BtorPtrHashTable *subst)
{
  assert (btor);
  assert (subst);

  int i;
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

  start = btor_time_stamp ();
  mm    = btor->mm;

  mark = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (mm, roots);
  BTOR_INIT_QUEUE (mm, queue);

  btor_init_ptr_hash_table_iterator (&hit, subst);
  while (btor_has_next_ptr_hash_table_iterator (&hit))
  {
    cur = BTOR_REAL_ADDR_NODE (btor_next_ptr_hash_table_iterator (&hit));
    BTOR_ENQUEUE (queue, cur);
  }

  /* mark cone and copy roots */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!btor_is_proxy_node (cur));

    if (!btor_contains_int_hash_map (mark, cur->id))
    {
      btor_add_int_hash_map (mark, cur->id);

      if (cur->parents == 0) BTOR_PUSH_STACK (roots, btor_copy_exp (btor, cur));

      btor_init_parent_iterator (&it, cur);
      while (btor_has_next_parent_iterator (&it))
      {
        cur_parent = btor_next_parent_iterator (&it);
        BTOR_ENQUEUE (queue, cur_parent);
      }
    }
  }

  btor_init_ptr_hash_table_iterator (&hit, subst);
  while (btor_has_next_ptr_hash_table_iterator (&hit))
  {
    cur = BTOR_REAL_ADDR_NODE (btor_next_ptr_hash_table_iterator (&hit));
    d   = btor_get_int_hash_map (mark, cur->id);
    assert (d);
    BTOR_ENQUEUE (queue, btor_copy_exp (btor, cur));
    d->as_int = 1; /* mark as enqueued */
  }

  /* rebuild bottom-up */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!btor_is_proxy_node (cur));
    assert (btor_contains_int_hash_map (mark, cur->id));
    assert (btor_get_int_hash_map (mark, cur->id)->as_int == 1);

    if (cur->refs == 1)
    {
      btor_release_exp (btor, cur);
      continue;
    }

    if (all_exps_below_rebuilt (btor, cur, mark))
    {
      btor_remove_int_hash_map (mark, cur->id, 0);
      btor_release_exp (btor, cur);

      /* traverse upwards and enqueue all parents that are not yet
       * in the queue. */
      btor_init_parent_iterator (&it, cur);
      while (btor_has_next_parent_iterator (&it))
      {
        cur_parent = btor_next_parent_iterator (&it);
        d          = btor_get_int_hash_map (mark, cur_parent->id);
        if (d && d->as_int == 1) continue;
        assert (!d || d->as_int == 0);
        if (!d) d = btor_add_int_hash_map (mark, cur_parent->id);
        d->as_int = 1;
        BTOR_ENQUEUE (queue, btor_copy_exp (btor, cur_parent));
      }

      if ((sub = btor_find_substitution (btor, cur)))
        rebuilt_exp = btor_copy_exp (btor, sub);
      else
        rebuilt_exp = rebuild_exp (btor, cur);

      assert (btor_exp_get_sort_id (cur) == btor_exp_get_sort_id (rebuilt_exp));
      assert (rebuilt_exp);
      if (rebuilt_exp != cur)
      {
        simplified = btor_simplify_exp (btor, rebuilt_exp);
        // TODO: only push new roots? use hash table for roots instead of
        // stack?
        if (cur->parents == 0)
          BTOR_PUSH_STACK (roots, btor_copy_exp (btor, cur));

        set_simplified_exp (btor, cur, simplified);
      }
      btor_release_exp (btor, rebuilt_exp);
    }
    /* not all children rebuilt, enqueue again */
    else
      BTOR_ENQUEUE (queue, cur);
  }

  BTOR_RELEASE_QUEUE (queue);

  for (i = 0; i < BTOR_COUNT_STACK (roots); i++)
  {
    cur = BTOR_PEEK_STACK (roots, i);
    btor_release_exp (btor, cur);
  }

  BTOR_RELEASE_STACK (roots);

  assert (btor_check_unique_table_children_proxy_free_dbg (btor));
  btor_delete_int_hash_map (mark);

  update_node_hash_tables (btor);
  assert (btor_check_lambdas_static_rho_proxy_free_dbg (btor));
  btor->time.subst_rebuild += btor_time_stamp () - start;
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

  btor_init_ptr_hash_table_iterator (&it, btor->embedded_constraints);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    assert (BTOR_REAL_ADDR_NODE (cur)->constraint);
    /* embedded constraints have possibly lost their parents,
     * e.g. top conjunction of constraints that are released */
    if (BTOR_REAL_ADDR_NODE (cur)->parents > 0) btor->stats.ec_substitutions++;
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
  int count;

  if (btor->embedded_constraints->count > 0u)
  {
    start = btor_time_stamp ();
    count = 0;
    BTOR_INIT_STACK (btor->mm, ec);
    btor_init_ptr_hash_table_iterator (&it, btor->embedded_constraints);
    while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      cur = btor_copy_exp (btor, btor_next_ptr_hash_table_iterator (&it));
      BTOR_PUSH_STACK (ec, cur);
    }

    /* Note: it may happen that new embedded constraints are inserted into
     *       btor->embedded_constraints here. */
    substitute_embedded_constraints (btor);

    while (!BTOR_EMPTY_STACK (ec))
    {
      cur = BTOR_POP_STACK (ec);

      if (btor_get_ptr_hash_table (btor->embedded_constraints, cur))
      {
        count++;
        btor_remove_ptr_hash_table (btor->embedded_constraints, cur, 0, 0);
        btor_insert_unsynthesized_constraint (btor, cur);
        btor_release_exp (btor, cur);
      }
      btor_release_exp (btor, cur);
    }
    BTOR_RELEASE_STACK (ec);

    delta = btor_time_stamp () - start;
    btor->time.embedded += delta;
    BTOR_MSG (btor->msg,
              1,
              "replaced %d embedded constraints in %1.f seconds",
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

  ass = btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
  btor_init_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    if (BTOR_REAL_ADDR_NODE (cur)->simplified)
    {
      /* Note: do not simplify constraint expression in order to prevent
       * constraint expressions from not being added to btor->assumptions.
       */
      simp = btor_pointer_chase_simplified_exp (btor, cur);
      if (!btor_get_ptr_hash_table (ass, simp))
        btor_add_ptr_hash_table (ass, btor_copy_exp (btor, simp));
      btor_release_exp (btor, cur);
    }
    else
    {
      if (!btor_get_ptr_hash_table (ass, cur))
        btor_add_ptr_hash_table (ass, cur);
      else
        btor_release_exp (btor, cur);
    }
  }
  btor_delete_ptr_hash_table (btor->assumptions);
  btor->assumptions = ass;
}

int
btor_simplify (Btor *btor)
{
  assert (btor);

  BtorSolverResult result;
  int rounds;
  double start, delta;
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  int skelrounds = 0;
#endif

  rounds = 0;
  start  = btor_time_stamp ();

  if (btor->inconsistent) goto DONE;

  /* empty varsubst_constraints table if variable substitution was disabled
   * after adding variable substitution constraints (they are still in
   * unsynthesized_constraints).
   */
  if (btor_get_opt (btor, BTOR_OPT_VAR_SUBST) == 0
      && btor->varsubst_constraints->count > 0)
  {
    btor_delete_ptr_hash_table (btor->varsubst_constraints);
    btor->varsubst_constraints =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
  }

  do
  {
    rounds++;
    assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
    assert (btor_check_all_hash_tables_simp_free_dbg (btor));
    assert (btor_check_unique_table_children_proxy_free_dbg (btor));
    if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 1)
    {
      if (btor_get_opt (btor, BTOR_OPT_VAR_SUBST))
      {
        substitute_var_exps (btor);
        assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
        assert (btor_check_all_hash_tables_simp_free_dbg (btor));
        assert (btor_check_unique_table_children_proxy_free_dbg (btor));

        if (btor->inconsistent) break;

        if (btor->varsubst_constraints->count)
          break;  // TODO (ma): continue instead of break?
      }

      process_embedded_constraints (btor);
      assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
      assert (btor_check_all_hash_tables_simp_free_dbg (btor));
      assert (btor_check_unique_table_children_proxy_free_dbg (btor));

      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) continue;
    }

    if (btor_get_opt (btor, BTOR_OPT_ELIMINATE_SLICES)
        && btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && !btor_get_opt (btor, BTOR_OPT_INCREMENTAL))
    {
      btor_eliminate_slices_on_bv_vars (btor);
      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count
          || btor->embedded_constraints->count)
        continue;
    }

#ifndef BTOR_DO_NOT_PROCESS_SKELETON
    if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_get_opt (btor, BTOR_OPT_SKELETON_PREPROC))
    {
      skelrounds++;
      if (skelrounds <= 1)  // TODO only one?
      {
        btor_process_skeleton (btor);
        assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
        assert (btor_check_all_hash_tables_simp_free_dbg (btor));
        assert (btor_check_unique_table_children_proxy_free_dbg (btor));
        if (btor->inconsistent) break;
      }

      if (btor->varsubst_constraints->count
          || btor->embedded_constraints->count)
        continue;
    }
#endif

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    if (btor_get_opt (btor, BTOR_OPT_UCOPT)
        && btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && !btor_get_opt (btor, BTOR_OPT_INCREMENTAL)
        && !btor_get_opt (btor, BTOR_OPT_MODEL_GEN))
    {
      btor_optimize_unconstrained (btor);
      assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
      assert (btor_check_all_hash_tables_simp_free_dbg (btor));
      assert (btor_check_unique_table_children_proxy_free_dbg (btor));
      if (btor->inconsistent) break;
    }

    if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_get_opt (btor, BTOR_OPT_EXTRACT_LAMBDAS))
      btor_extract_lambdas (btor);

    if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_get_opt (btor, BTOR_OPT_MERGE_LAMBDAS))
      btor_merge_lambdas (btor);

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    /* rewrite/beta-reduce applies on lambdas */
    if (btor_get_opt (btor, BTOR_OPT_BETA_REDUCE_ALL))
      btor_eliminate_applies (btor);

    /* add ackermann constraints for all uninterpreted functions */
    if (btor_get_opt (btor, BTOR_OPT_ACKERMANN))
      btor_add_ackermann_constraints (btor);
  } while (btor->varsubst_constraints->count
           || btor->embedded_constraints->count);

DONE:
  delta = btor_time_stamp () - start;
  btor->time.rewrite += delta;
  BTOR_MSG (btor->msg, 1, "%d rewriting rounds in %.1f seconds", rounds, delta);

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

/* bit vector skeleton is always encoded, i.e., if BTOR_IS_SYNTH_NODE is true,
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
  unsigned int count, i, len;
  int same_children_mem, j;
  int invert_av0 = 0;
  int invert_av1 = 0;
  int invert_av2 = 0;
  double start;
  bool restart, opt_lazy_synth;
  BtorIntHashTable *cache;

  assert (btor);
  assert (exp);

  start          = btor_time_stamp ();
  mm             = btor->mm;
  avmgr          = btor->avmgr;
  count          = 0;
  cache          = btor_new_int_hash_table (mm);
  opt_lazy_synth = btor_get_opt (btor, BTOR_OPT_FUN_LAZY_SYNTHESIZE) == 1;

  BTOR_INIT_STACK (mm, exp_stack);
  BTOR_PUSH_STACK (exp_stack, exp);
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));

  while (!BTOR_EMPTY_STACK (exp_stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (exp_stack));

    if (BTOR_IS_SYNTH_NODE (cur)) continue;

    count++;
    if (!btor_contains_int_hash_table (cache, cur->id))
    {
      if (btor_is_bv_const_node (cur))
      {
        cur->av = btor_const_aigvec (avmgr, btor_const_get_bits (cur));
        BTORLOG (2, "  synthesized: %s", node2string (cur));
        /* no need to call btor_aigvec_to_sat_tseitin here */
      }
      /* encode bv skeleton inputs: var, apply, feq */
      else if (btor_is_bv_var_node (cur)
               || (btor_is_apply_node (cur) && !cur->parameterized)
               || btor_is_fun_eq_node (cur))
      {
        assert (!cur->parameterized);
        cur->av = btor_var_aigvec (avmgr, btor_get_exp_width (btor, cur));

        if (btor_is_bv_var_node (cur) && backannotation
            && (name = btor_get_symbol_exp (btor, cur)))
        {
          len = strlen (name) + 40;
          if (btor_get_exp_width (btor, cur) > 1)
          {
            indexed_name = btor_malloc (mm, len);
            for (i = 0; i < cur->av->len; i++)
            {
              b = btor_add_ptr_hash_table (backannotation, cur->av->aigs[i]);
              assert (b->key == cur->av->aigs[i]);
              sprintf (indexed_name, "%s[%d]", name, i);
              b->data.as_str = btor_strdup (mm, indexed_name);
            }
            btor_free (mm, indexed_name, len);
          }
          else
          {
            assert (btor_get_exp_width (btor, cur) == 1);
            b = btor_add_ptr_hash_table (backannotation, cur->av->aigs[0]);
            assert (b->key == cur->av->aigs[0]);
            b->data.as_str = btor_strdup (mm, name);
          }
        }
        BTORLOG (2, "  synthesized: %s", node2string (cur));
        btor_aigvec_to_sat_tseitin (avmgr, cur->av);

        /* continue synthesizing children for apply and feq nodes if
         * lazy_synthesize is disabled */
        if (!opt_lazy_synth) goto PUSH_CHILDREN;
      }
      /* we stop at function nodes as they will be lazily synthesized and
       * encoded during consistency checking */
      else if (btor_is_fun_node (cur) && opt_lazy_synth)
      {
        continue;
      }
      else
      {
      PUSH_CHILDREN:
        assert (!opt_lazy_synth || !btor_is_fun_node (cur));

        btor_add_int_hash_table (cache, cur->id);
        BTOR_PUSH_STACK (exp_stack, cur);
        for (j = cur->arity - 1; j >= 0; j--)
          BTOR_PUSH_STACK (exp_stack, cur->e[j]);

        /* synthesize nodes in static_rho of lambda nodes */
        if (btor_is_lambda_node (cur))
        {
          static_rho = btor_lambda_get_static_rho (cur);
          if (static_rho)
          {
            btor_init_ptr_hash_table_iterator (&it, static_rho);
            while (btor_has_next_ptr_hash_table_iterator (&it))
            {
              value = it.bucket->data.as_ptr;
              args  = btor_next_ptr_hash_table_iterator (&it);
              BTOR_PUSH_STACK (exp_stack, btor_simplify_exp (btor, value));
              BTOR_PUSH_STACK (exp_stack, btor_simplify_exp (btor, args));
            }
          }
        }
      }
    }
    /* paremterized nodes, argument nodes and functions are not
     * synthesizable */
    else if (!cur->parameterized && !btor_is_args_node (cur)
             && !btor_is_fun_node (cur))
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
          if (!BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (cur->e[i])))
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
        assert (btor_is_slice_node (cur));
        invert_av0 = BTOR_IS_INVERTED_NODE (cur->e[0]);
        av0        = BTOR_REAL_ADDR_NODE (cur->e[0])->av;
        if (invert_av0) btor_invert_aigvec (avmgr, av0);
        cur->av = btor_slice_aigvec (
            avmgr, av0, btor_slice_get_upper (cur), btor_slice_get_lower (cur));
        if (invert_av0) btor_invert_aigvec (avmgr, av0);
      }
      else if (cur->arity == 2)
      {
        /* We have to check if the children are in the same memory
         * place if they are in the same memory place. Then we need to
         * allocate memory for the AIG vectors if they are not, then
         * we can invert them in place and invert them back afterwards
         * (only if necessary) .
         */
        same_children_mem =
            BTOR_REAL_ADDR_NODE (cur->e[0]) == BTOR_REAL_ADDR_NODE (cur->e[1]);
        if (same_children_mem)
        {
          av0 = BTOR_AIGVEC_NODE (btor, cur->e[0]);
          av1 = BTOR_AIGVEC_NODE (btor, cur->e[1]);
        }
        else
        {
          invert_av0 = BTOR_IS_INVERTED_NODE (cur->e[0]);
          av0        = BTOR_REAL_ADDR_NODE (cur->e[0])->av;
          if (invert_av0) btor_invert_aigvec (avmgr, av0);
          invert_av1 = BTOR_IS_INVERTED_NODE (cur->e[1]);
          av1        = BTOR_REAL_ADDR_NODE (cur->e[1])->av;
          if (invert_av1) btor_invert_aigvec (avmgr, av1);
        }
        switch (cur->kind)
        {
          case BTOR_AND_NODE:
            cur->av = btor_and_aigvec (avmgr, av0, av1);
            break;
          case BTOR_BV_EQ_NODE:
            cur->av = btor_eq_aigvec (avmgr, av0, av1);
            break;
          case BTOR_ADD_NODE:
            cur->av = btor_add_aigvec (avmgr, av0, av1);
            break;
          case BTOR_MUL_NODE:
            cur->av = btor_mul_aigvec (avmgr, av0, av1);
            break;
          case BTOR_ULT_NODE:
            cur->av = btor_ult_aigvec (avmgr, av0, av1);
            break;
          case BTOR_SLL_NODE:
            cur->av = btor_sll_aigvec (avmgr, av0, av1);
            break;
          case BTOR_SRL_NODE:
            cur->av = btor_srl_aigvec (avmgr, av0, av1);
            break;
          case BTOR_UDIV_NODE:
            cur->av = btor_udiv_aigvec (avmgr, av0, av1);
            break;
          case BTOR_UREM_NODE:
            cur->av = btor_urem_aigvec (avmgr, av0, av1);
            break;
          default:
            assert (cur->kind == BTOR_CONCAT_NODE);
            cur->av = btor_concat_aigvec (avmgr, av0, av1);
            break;
        }

        if (same_children_mem)
        {
          btor_release_delete_aigvec (avmgr, av0);
          btor_release_delete_aigvec (avmgr, av1);
        }
        else
        {
          if (invert_av0) btor_invert_aigvec (avmgr, av0);
          if (invert_av1) btor_invert_aigvec (avmgr, av1);
        }
        if (!opt_lazy_synth) btor_aigvec_to_sat_tseitin (avmgr, cur->av);
      }
      else
      {
        assert (cur->arity == 3);

        if (btor_is_bv_cond_node (cur))
        {
          same_children_mem =
              BTOR_REAL_ADDR_NODE (cur->e[0]) == BTOR_REAL_ADDR_NODE (cur->e[1])
              || BTOR_REAL_ADDR_NODE (cur->e[0])
                     == BTOR_REAL_ADDR_NODE (cur->e[2])
              || BTOR_REAL_ADDR_NODE (cur->e[1])
                     == BTOR_REAL_ADDR_NODE (cur->e[2]);
          if (same_children_mem)
          {
            av0 = BTOR_AIGVEC_NODE (btor, cur->e[0]);
            av1 = BTOR_AIGVEC_NODE (btor, cur->e[1]);
            av2 = BTOR_AIGVEC_NODE (btor, cur->e[2]);
          }
          else
          {
            invert_av0 = BTOR_IS_INVERTED_NODE (cur->e[0]);
            av0        = BTOR_REAL_ADDR_NODE (cur->e[0])->av;
            if (invert_av0) btor_invert_aigvec (avmgr, av0);
            invert_av1 = BTOR_IS_INVERTED_NODE (cur->e[1]);
            av1        = BTOR_REAL_ADDR_NODE (cur->e[1])->av;
            if (invert_av1) btor_invert_aigvec (avmgr, av1);
            invert_av2 = BTOR_IS_INVERTED_NODE (cur->e[2]);
            av2        = BTOR_REAL_ADDR_NODE (cur->e[2])->av;
            if (invert_av2) btor_invert_aigvec (avmgr, av2);
          }
          cur->av = btor_cond_aigvec (avmgr, av0, av1, av2);
          if (same_children_mem)
          {
            btor_release_delete_aigvec (avmgr, av2);
            btor_release_delete_aigvec (avmgr, av1);
            btor_release_delete_aigvec (avmgr, av0);
          }
          else
          {
            if (invert_av0) btor_invert_aigvec (avmgr, av0);
            if (invert_av1) btor_invert_aigvec (avmgr, av1);
            if (invert_av2) btor_invert_aigvec (avmgr, av2);
          }
        }
      }
      assert (cur->av);
      BTORLOG (2, "  synthesized: %s", node2string (cur));
      btor_aigvec_to_sat_tseitin (avmgr, cur->av);
    }
  }
  BTOR_RELEASE_STACK (exp_stack);
  btor_delete_int_hash_table (cache);

  if (count > 0 && btor_get_opt (btor, BTOR_OPT_VERBOSITY) > 3)
    BTOR_MSG (
        btor->msg, 3, "synthesized %u expressions into AIG vectors", count);

  btor->time.synth_exp += btor_time_stamp () - start;
}

/* forward assumptions to the SAT solver */
void
btor_add_again_assumptions (Btor *btor)
{
  assert (btor);
  assert (btor_check_assumptions_simp_free_dbg (btor));

  int i;
  BtorNode *exp, *cur, *e;
  BtorNodePtrStack stack;
  BtorPtrHashTable *assumptions;
  BtorPtrHashTableIterator it;
  BtorAIG *aig;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorIntHashTable *mark;

  amgr = btor_get_aig_mgr_btor (btor);
  smgr = btor_get_sat_mgr_btor (btor);

  BTOR_INIT_STACK (btor->mm, stack);
  mark = btor_new_int_hash_table (btor->mm);

  assumptions = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  btor_init_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    exp = btor_next_ptr_hash_table_iterator (&it);
    assert (!BTOR_REAL_ADDR_NODE (btor_is_proxy_node (exp)));

    if (BTOR_IS_INVERTED_NODE (exp) || !btor_is_and_node (exp))
    {
      if (!btor_get_ptr_hash_table (assumptions, exp))
        btor_add_ptr_hash_table (assumptions, exp);
    }
    else
    {
      BTOR_PUSH_STACK (stack, exp);
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_POP_STACK (stack);
        assert (!BTOR_IS_INVERTED_NODE (cur));
        assert (btor_is_and_node (cur));
        if (btor_contains_int_hash_table (mark, cur->id)) continue;
        btor_add_int_hash_table (mark, cur->id);
        for (i = 0; i < 2; i++)
        {
          e = cur->e[i];
          if (!BTOR_IS_INVERTED_NODE (e) && btor_is_and_node (e))
            BTOR_PUSH_STACK (stack, e);
          else if (!btor_get_ptr_hash_table (assumptions, e))
            btor_add_ptr_hash_table (assumptions, e);
        }
      }
    }
  }

  btor_init_ptr_hash_table_iterator (&it, assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    assert (btor_get_exp_width (btor, cur) == 1);
    assert (!BTOR_REAL_ADDR_NODE (cur)->simplified);
    aig = exp_to_aig (btor, cur);
    btor_aig_to_sat (amgr, aig);
    if (aig == BTOR_AIG_TRUE) continue;
    if (btor_is_initialized_sat (smgr))
    {
      assert (btor_aig_get_cnf_id (aig) != 0);
      btor_assume_sat (smgr, btor_aig_get_cnf_id (aig));
    }
    btor_release_aig (amgr, aig);
  }

  BTOR_RELEASE_STACK (stack);
  btor_delete_ptr_hash_table (assumptions);
  btor_delete_int_hash_table (mark);
}

#if 0
/* updates SAT assignments, reads assumptions and
 * returns if an assignment has changed
 */
static int
update_sat_assignments (Btor * btor)
{
  assert (btor);

  BtorSATMgr *smgr;

  smgr = btor_get_sat_mgr_btor (btor);
  add_again_assumptions (btor);
#ifndef NDEBUG
  int result;
  result = timed_sat_sat (btor, -1);
  assert (result == BTOR_SAT);
#else
  (void) timed_sat_sat (btor, -1);
#endif
  return btor_changed_sat (smgr);
}
#endif

int
btor_sat_btor (Btor *btor, int lod_limit, int sat_limit)
{
  assert (btor);
  assert (btor_get_opt (btor, BTOR_OPT_INCREMENTAL)
          || btor->btor_sat_btor_called == 0);

  BtorSolverResult res;
  uint32_t engine;

  engine = btor_get_opt (btor, BTOR_OPT_ENGINE);

  if (!btor->slv)
  {
    /* eliminate lambdas (define-fun) in the QF_BV case */
    if (btor->ufs->count == 0 && btor->lambdas->count > 0)
      btor_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

    /* these engines work on QF_BV only */
    if (engine == BTOR_ENGINE_SLS && btor->ufs->count == 0)
    {
      assert (btor->lambdas->count == 0
              || btor_get_opt (btor, BTOR_OPT_BETA_REDUCE_ALL));
      btor->slv = btor_new_sls_solver (btor);
    }
    else if (engine == BTOR_ENGINE_PROP && btor->ufs->count == 0)
    {
      assert (btor->lambdas->count == 0
              || btor_get_opt (btor, BTOR_OPT_BETA_REDUCE_ALL));
      btor->slv = btor_new_prop_solver (btor);
    }
    else if (engine == BTOR_ENGINE_AIGPROP && btor->ufs->count == 0)
    {
      assert (btor->lambdas->count == 0
              || btor_get_opt (btor, BTOR_OPT_BETA_REDUCE_ALL));
      btor->slv = btor_new_aigprop_solver (btor);
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

#ifndef NDEBUG
  Btor *uclone = 0;
  if (btor_get_opt (btor, BTOR_OPT_CHK_UNCONSTRAINED)
      && btor_get_opt (btor, BTOR_OPT_UCOPT)
      && btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 2
      && !btor_get_opt (btor, BTOR_OPT_INCREMENTAL)
      && !btor_get_opt (btor, BTOR_OPT_MODEL_GEN))
  {
    uclone = btor_clone_btor (btor);
    btor_set_opt (uclone, BTOR_OPT_UCOPT, 0);
  }

  Btor *mclone             = 0;
  BtorPtrHashTable *inputs = 0;
  if (btor_get_opt (btor, BTOR_OPT_CHK_MODEL))
  {
    mclone = btor_clone_exp_layer (btor, 0);
    btor_set_opt (mclone, BTOR_OPT_LOGLEVEL, 0);
    btor_set_opt (mclone, BTOR_OPT_VERBOSITY, 0);
    btor_set_opt (mclone, BTOR_OPT_FUN_DUAL_PROP, 0);
    inputs = map_inputs_check_model (btor, mclone);
  }
#endif

#ifndef NBTORLOG
  btor_log_opts (btor);
#endif
  res = btor->slv->api.sat (btor->slv);
  btor->btor_sat_btor_called++;

  if (btor_get_opt (btor, BTOR_OPT_MODEL_GEN) && res == BTOR_RESULT_SAT)
  {
    switch (btor_get_opt (btor, BTOR_OPT_ENGINE))
    {
      case BTOR_ENGINE_SLS:
      case BTOR_ENGINE_PROP:
      case BTOR_ENGINE_AIGPROP:
        btor->slv->api.generate_model (
            btor->slv, btor_get_opt (btor, BTOR_OPT_MODEL_GEN) == 2, false);
        break;
      default:
        btor->slv->api.generate_model (
            btor->slv, btor_get_opt (btor, BTOR_OPT_MODEL_GEN) == 2, true);
    }
  }

#ifndef NDEBUG
  if (uclone)
  {
    assert (btor_get_opt (btor, BTOR_OPT_UCOPT));
    assert (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 2);
    assert (!btor_get_opt (btor, BTOR_OPT_INCREMENTAL));
    assert (!btor_get_opt (btor, BTOR_OPT_MODEL_GEN));
    BtorSolverResult ucres = uclone->slv->api.sat (uclone->slv);
    assert (res == ucres);
  }

  if (mclone)
  {
    assert (inputs);
    if (res == BTOR_RESULT_SAT && !btor_get_opt (btor, BTOR_OPT_UCOPT))
    {
      if (!btor_get_opt (btor, BTOR_OPT_MODEL_GEN))
      {
        switch (btor_get_opt (btor, BTOR_OPT_ENGINE))
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
    btor_init_ptr_hash_table_iterator (&it, inputs);
    while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      btor_release_exp (btor, (BtorNode *) it.bucket->data.as_ptr);
      btor_release_exp (mclone, btor_next_ptr_hash_table_iterator (&it));
    }
    btor_delete_ptr_hash_table (inputs);
    btor_delete_btor (mclone);
  }
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_CHK_FAILED_ASSUMPTIONS)
      && !btor->inconsistent && btor->last_sat_result == BTOR_RESULT_UNSAT)
    check_failed_assumptions (btor);
#endif
  return res;
}

static int
is_valid_argument (Btor *btor, BtorNode *exp)
{
  exp = BTOR_REAL_ADDR_NODE (exp);
  if (btor_is_fun_node (btor_simplify_exp (btor, exp))) return 0;
  if (btor_is_array_node (btor_simplify_exp (btor, exp))) return 0;
  /* scope of bound parmaters already closed (cannot be used anymore) */
  if (btor_is_param_node (exp) && btor_param_is_bound (exp)) return 0;
  return 1;
}

int32_t
btor_fun_sort_check (Btor *btor, BtorNode *args[], uint32_t argc, BtorNode *fun)
{
  (void) btor;
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (btor_is_fun_node (btor_simplify_exp (btor, fun)));
  assert (argc == btor_get_fun_arity (btor, fun));

  uint32_t i, pos = -1;
  BtorSortId sort;
  BtorTupleSortIterator it;

  assert (btor_is_tuple_sort (
      btor, btor_get_domain_fun_sort (btor, btor_exp_get_sort_id (fun))));
  btor_init_tuple_sort_iterator (
      &it, btor, btor_get_domain_fun_sort (btor, btor_exp_get_sort_id (fun)));
  for (i = 0; i < argc; i++)
  {
    assert (btor_has_next_tuple_sort_iterator (&it));
    sort = btor_next_tuple_sort_iterator (&it);
    /* NOTE: we do not allow functions or arrays as arguments yet */
    if (!is_valid_argument (btor, args[i])
        || sort != btor_exp_get_sort_id (args[i]))
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
  assert (btor_get_exp_width (btor, exp) == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  amgr = btor_get_aig_mgr_btor (btor);

  btor_synthesize_exp (btor, exp, 0);
  av = BTOR_REAL_ADDR_NODE (exp)->av;

  assert (av);
  assert (av->len == 1);

  result = av->aigs[0];

  if (BTOR_IS_INVERTED_NODE (exp))
    result = btor_not_aig (amgr, result);
  else
    result = btor_copy_aig (amgr, result);

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
  result = BTOR_REAL_ADDR_NODE (exp)->av;
  assert (result);

  if (BTOR_IS_INVERTED_NODE (exp))
    result = btor_not_aigvec (avmgr, result);
  else
    result = btor_copy_aigvec (avmgr, result);

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

  inputs = btor_new_ptr_hash_table (clone->mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

  btor_init_ptr_hash_table_iterator (&it, clone->bv_vars);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    b   = btor_get_ptr_hash_table (btor->bv_vars, cur);
    assert (b);

    assert (!btor_get_ptr_hash_table (inputs, cur));
    btor_add_ptr_hash_table (inputs, btor_copy_exp (clone, cur))->data.as_ptr =
        btor_copy_exp (btor, (BtorNode *) b->key);
  }

  btor_init_ptr_hash_table_iterator (&it, clone->ufs);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    b   = btor_get_ptr_hash_table (btor->ufs, cur);
    assert (b);

    assert (!btor_get_ptr_hash_table (inputs, cur));
    btor_add_ptr_hash_table (inputs, btor_copy_exp (clone, cur))->data.as_ptr =
        btor_copy_exp (btor, (BtorNode *) b->key);
  }

  return inputs;
}

static void
rebuild_formula (Btor *btor, int rewrite_level)
{
  assert (btor);

  int i;
  BtorNode *cur;
  BtorPtrHashTable *t;

  /* set new rewrite level */
  btor_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rewrite_level);

  t = btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);

  /* collect all leaves and rebuild whole formula */
  for (i = BTOR_COUNT_STACK (btor->nodes_id_table) - 1; i >= 0; i--)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;

    if (btor_is_proxy_node (cur)) continue;

    if (cur->arity == 0)
    {
      assert (btor_is_bv_var_node (cur) || btor_is_bv_const_node (cur)
              || btor_is_param_node (cur) || btor_is_uf_node (cur));
      btor_add_ptr_hash_table (t, cur);
    }
  }

  substitute_and_rebuild (btor, t);
  btor_delete_ptr_hash_table (t);
}

static void
check_model (Btor *btor, Btor *clone, BtorPtrHashTable *inputs)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_RESULT_SAT);
  assert (clone);
  assert (inputs);

  uint32_t i;
  int ret;
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
  btor_init_ptr_hash_table_iterator (&it, clone->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    btor_assert_exp (clone, btor_next_ptr_hash_table_iterator (&it));
  btor_reset_assumptions (clone);

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0) substitute_var_exps (clone);

  /* rebuild formula with new rewriting level */
  rebuild_formula (clone, 3);

  /* add bit vector variable models */
  BTOR_INIT_STACK (clone->mm, consts);
  btor_init_ptr_hash_table_iterator (&it, inputs);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    exp = (BtorNode *) it.bucket->data.as_ptr;
    assert (exp);
    assert (BTOR_IS_REGULAR_NODE (exp));
    assert (exp->btor == btor);
    /* Note: we do not want simplified constraints here */
    simp = btor_pointer_chase_simplified_exp (btor, exp);
    cur  = btor_next_ptr_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->btor == clone);
    simp_clone      = btor_simplify_exp (clone, cur);
    real_simp_clone = BTOR_REAL_ADDR_NODE (simp_clone);

    if (btor_is_fun_node (real_simp_clone))
    {
      fmodel = btor_get_fun_model (btor, simp);
      if (!fmodel) continue;

      BTORLOG (2, "assert model for %s", node2string (real_simp_clone));
      btor_init_ptr_hash_table_iterator (&it, (BtorPtrHashTable *) fmodel);
      while (btor_has_next_ptr_hash_table_iterator (&it))
      {
        value      = (BtorBitVector *) it.bucket->data.as_ptr;
        args_tuple = btor_next_ptr_hash_table_iterator (&it);

        /* create condition */
        assert (BTOR_EMPTY_STACK (consts));
        for (i = 0; i < args_tuple->arity; i++)
        {
          model = btor_const_exp (clone, args_tuple->bv[i]);
          BTOR_PUSH_STACK (consts, model);
        }

        args  = btor_args_exp (clone, consts.start, BTOR_COUNT_STACK (consts));
        apply = btor_apply_exp (clone, real_simp_clone, args);
        model = btor_const_exp (clone, value);
        eq    = btor_eq_exp (clone, apply, model);
        btor_assert_exp (clone, eq);
        btor_release_exp (clone, eq);
        btor_release_exp (clone, model);
        btor_release_exp (clone, apply);
        btor_release_exp (clone, args);

        while (!BTOR_EMPTY_STACK (consts))
          btor_release_exp (clone, BTOR_POP_STACK (consts));
      }
    }
    else
    {
      BTORLOG (2,
               "assert model for %s (%s)",
               node2string (real_simp_clone),
               btor_get_symbol_exp (clone, cur));
      /* we need to invert the assignment if simplified is inverted */
      model =
          btor_const_exp (clone,
                          (BtorBitVector *) btor_get_bv_model (
                              btor, BTOR_COND_INVERT_NODE (simp_clone, simp)));
      eq = btor_eq_exp (clone, real_simp_clone, model);
      btor_assert_exp (clone, eq);
      btor_release_exp (clone, eq);
      btor_release_exp (clone, model);
    }
  }
  BTOR_RELEASE_STACK (consts);

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0) substitute_var_exps (clone);

  btor_set_opt (clone, BTOR_OPT_BETA_REDUCE_ALL, 1);
  ret = btor_simplify (clone);

  // btor_print_model (btor, "btor", stdout);
  assert (ret != BTOR_RESULT_UNKNOWN
          || clone->slv->api.sat (clone->slv) == BTOR_RESULT_SAT);
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

  clone = btor_clone_exp_layer (btor, 0);
  btor_set_opt (clone, BTOR_OPT_LOGLEVEL, 0);
  btor_set_opt (clone, BTOR_OPT_VERBOSITY, 0);
  btor_set_opt (clone, BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0);
  btor_set_opt (clone, BTOR_OPT_FUN_DUAL_PROP, 0);

  /* assert failed assumptions */
  btor_init_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    ass = btor_next_ptr_hash_table_iterator (&it);
    if (btor_failed_exp (btor, ass))
    {
      cass = btor_match_node (clone, ass);
      assert (cass);
      btor_assert_exp (clone, cass);
      btor_release_exp (clone, cass);
    }
  }

  /* cleanup assumptions */
  btor_init_ptr_hash_table_iterator (&it, clone->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    btor_release_exp (clone, btor_next_ptr_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (clone->assumptions);
  clone->assumptions =
      btor_new_ptr_hash_table (clone->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);

  assert (clone->slv->api.sat (clone->slv) == BTOR_RESULT_UNSAT);
  btor_delete_btor (clone);
}
#endif

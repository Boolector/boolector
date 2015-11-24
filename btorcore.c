/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"
#include "btorbeta.h"
#include "btorbitvec.h"
#include "btorclone.h"
#include "btorconfig.h"
#include "btorconst.h"
#include "btordbg.h"
#include "btordcr.h"
#include "btorexit.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btormsg.h"
#include "btoropt.h"
#include "btorprintmodel.h"
#include "btorrewrite.h"
#include "btorsat.h"
#include "dumper/btordumpbtor.h"
#include "simplifier/btorack.h"
#include "simplifier/btorelimapplies.h"
#include "simplifier/btorelimslices.h"
#include "simplifier/btorextract.h"
#include "simplifier/btormerge.h"
#include "simplifier/btorunconstrained.h"
#include "utils/btorinthash.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorparamcache.h"
#include "utils/btorutil.h"

#include <limits.h>

/*------------------------------------------------------------------------*/

#ifndef BTOR_USE_LINGELING
#define BTOR_DO_NOT_PROCESS_SKELETON
#endif

#ifndef BTOR_DO_NOT_PROCESS_SKELETON
#include "simplifier/btorskel.h"
#endif

#if !defined(NDEBUG) && defined(BTOR_USE_LINGELING)
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
#define BTOR_CHECK_UNCONSTRAINED
#endif
#define BTOR_CHECK_MODEL
#define BTOR_CHECK_DUAL_PROP
#endif
#undef BTOR_CHECK_FAILED

#define DP_QSORT_JUST 0
#define DP_QSORT_ASC 1
#define DP_QSORT_DESC 2
#define DP_QSORT_ASC_DESC_FIRST 3
#define DP_QSORT_ASC_DESC_ALW 4
#define DP_QSORT DP_QSORT_JUST

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
    BTOR_INIT_STACK (table.id2sort);           \
    BTOR_PUSH_STACK (mm, table.id2sort, 0);    \
  } while (0)

#define BTOR_RELEASE_SORT_UNIQUE_TABLE(mm, table) \
  do                                              \
  {                                               \
    BTOR_RELEASE_UNIQUE_TABLE (mm, table);        \
    BTOR_RELEASE_STACK (mm, table.id2sort);       \
  } while (0)

#define BTOR_ABORT_CORE(cond, msg)                   \
  do                                                 \
  {                                                  \
    if (cond)                                        \
    {                                                \
      printf ("[btorcore] %s: %s\n", __func__, msg); \
      fflush (stdout);                               \
      exit (BTOR_ERR_EXIT);                          \
    }                                                \
  } while (0)

#define BTOR_COND_INVERT_AIG_NODE(exp, aig) \
  ((BtorAIG *) (((unsigned long int) (exp) &1ul) ^ ((unsigned long int) (aig))))

/*------------------------------------------------------------------------*/

static BtorSolver *new_core_solver (Btor *);
static int sat_aux_btor_dual_prop (Btor *);
static BtorAIG *exp_to_aig (Btor *, BtorNode *);
static void synthesize_exp (Btor *, BtorNode *, BtorPtrHashTable *);

#ifdef BTOR_CHECK_MODEL
static void check_model (Btor *, Btor *, BtorPtrHashTable *);
static BtorPtrHashTable *map_inputs_check_model (Btor *, Btor *);
#endif

#ifdef BTOR_CHECK_FAILED
static void check_failed_assumptions (Btor *, Btor *);
#endif

#ifdef BTOR_CHECK_DUAL_PROP
static void check_dual_prop (Btor *, Btor *);
#endif
/*------------------------------------------------------------------------*/

const char *const g_btor_op2string[] = {
    "invalid",  //  0
    "const",    //  1
    "var",      //  2
    "param",    //  3
    "slice",    //  4
    "and",      //  5
    "beq",      //  6
    "aeq",      //  7
    "add",      //  8
    "mul",      //  9
    "ult",      // 10
    "sll",      // 11
    "srl",      // 12
    "udiv",     // 13
    "urem",     // 14
    "concat",   // 15
    "apply",    // 16
    "lambda",   // 17
    "bcond",    // 18
    "args",     // 19
    "uf",       // 20
    "proxy"     // 21
};

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
  BtorHashTableIterator it;

  btor_init_node_hash_table_iterator (&it, btor->substitutions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    btor_release_exp (btor, (BtorNode *) it.bucket->data.asPtr);
    cur = btor_next_node_hash_table_iterator (&it);
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
    b = btor_find_in_ptr_hash_table (btor->substitutions,
                                     BTOR_REAL_ADDR_NODE (exp));
    if (!b) break;
    result = BTOR_COND_INVERT_NODE (exp, (BtorNode *) b->data.asPtr);
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

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, subst);
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

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }
  BTOR_RELEASE_STACK (mm, visit);
  btor_free_int_hash_table (cache);
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
  assert (BTOR_REAL_ADDR_NODE (exp)->sort_id
          == BTOR_REAL_ADDR_NODE (subst)->sort_id);

  BtorNode *simp;
  BtorPtrHashBucket *b;
  exp = BTOR_REAL_ADDR_NODE (exp);

  if (exp == BTOR_REAL_ADDR_NODE (subst)) return;

  assert (substitution_cycle_check_dbg (btor, exp, subst));

  b = btor_find_in_ptr_hash_table (btor->substitutions, exp);
  if (update && b)
  {
    assert (b->data.asPtr);
    /* release data of current bucket */
    btor_release_exp (btor, (BtorNode *) b->data.asPtr);
    btor_remove_from_ptr_hash_table (btor->substitutions, exp, 0, 0);
    /* release key of current bucket */
    btor_release_exp (btor, exp);
  }
  else if (b)
  {
    assert ((BtorNode *) b->data.asPtr == subst);
    /* substitution already inserted */
    return;
  }

  simp = btor_find_substitution (btor, subst);

  if (simp) subst = simp;

  assert (!btor_find_in_ptr_hash_table (btor->substitutions,
                                        BTOR_REAL_ADDR_NODE (subst)));

  if (exp == BTOR_REAL_ADDR_NODE (subst)) return;

  btor_insert_in_ptr_hash_table (btor->substitutions, btor_copy_exp (btor, exp))
      ->data.asPtr = btor_copy_exp (btor, subst);
}

/*------------------------------------------------------------------------*/

static void
mark_exp (Btor *btor, BtorNode *exp, int new_mark)
{
  BtorMemMgr *mm;
  BtorNodePtrStack stack;
  BtorNode *cur;
  int i;

  assert (btor);
  assert (exp);

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  cur = BTOR_REAL_ADDR_NODE (exp);
  assert (!BTOR_IS_PROXY_NODE (cur));
  goto BTOR_MARK_NODE_ENTER_WITHOUT_POP;

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
  BTOR_MARK_NODE_ENTER_WITHOUT_POP:
    if (cur->mark != new_mark)
    {
      cur->mark = new_mark;
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

const char *
btor_version (Btor *btor)
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
  BTOR_CLR (&btor->stats);
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

  res = abs (btor->stats.oldconstraints.varsubst
             - btor->varsubst_constraints->count);

  res += abs (btor->stats.oldconstraints.embedded
              - btor->embedded_constraints->count);

  res += abs (btor->stats.oldconstraints.unsynthesized
              - btor->unsynthesized_constraints->count);

  res += abs (btor->stats.oldconstraints.synthesized
              - btor->synthesized_constraints->count);

  return res;
}

static void
report_constraint_stats (Btor *btor, int force)
{
  int changes;

  if (!force)
  {
    if (btor->options.verbosity.val <= 0) return;

    changes = constraints_stats_changes (btor);

    if (btor->options.verbosity.val == 1 && changes < 100000) return;

    if (btor->options.verbosity.val == 2 && changes < 1000) return;

    if (btor->options.verbosity.val == 3 && changes < 10) return;

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

  verbosity = btor->options.verbosity.val;

  report_constraint_stats (btor, 1);
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  if (btor->options.ucopt.val)
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
#endif
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
    assert (sizeof g_btor_op2string / sizeof *g_btor_op2string
            == BTOR_NUM_OPS_NODE);

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
                    g_btor_op2string[i],
                    btor->ops[i].cur,
                    btor->ops[i].max);
  }

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "bit blasting statistics:");
  BTOR_MSG (btor->msg,
            1,
            " AIG vectors (cur/max): %lld/%lld",
            btor->avmgr->cur_num_aigvecs,
            btor->avmgr->max_num_aigvecs);
  BTOR_MSG (btor->msg,
            1,
            " AIG ANDs (cur/max): %lld/%lld",
            btor->avmgr->amgr->cur_num_aigs,
            btor->avmgr->amgr->max_num_aigs);
  BTOR_MSG (btor->msg,
            1,
            " AIG variables: %lld",
            btor->avmgr->amgr->max_num_aig_vars);
  BTOR_MSG (
      btor->msg, 1, " CNF variables: %lld", btor->avmgr->amgr->num_cnf_vars);
  BTOR_MSG (
      btor->msg, 1, " CNF clauses: %lld", btor->avmgr->amgr->num_cnf_clauses);
  BTOR_MSG (
      btor->msg, 1, " CNF literals: %lld", btor->avmgr->amgr->num_cnf_literals);

  BTOR_MSG (btor->msg, 1, "");
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

  if (btor->slv) btor->slv->api.print_stats (btor);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "%.2f seconds beta-reduction", btor->time.beta);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds synthesize expressions",
            btor->time.synth_exp);
  BTOR_MSG (
      btor->msg, 1, "%.2f seconds reachable search", btor->time.reachable);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds determining failed assumptions",
            btor->time.failed);
  BTOR_MSG (btor->msg, 1, "%.2f seconds for cloning", btor->time.cloning);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds beta reduction probing",
            btor->time.br_probing);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds substitute and rebuild",
            btor->time.subst_rebuild);
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  if (btor->options.ucopt.val)
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds for unconstrained optimization",
              btor->time.ucopt);
#endif
  if (btor->options.model_gen.val)
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
            "%.2f seconds in beta reduction during rewriting (%.0f%%)",
            btor->time.betareduce,
            percent (btor->time.betareduce, btor->time.rewrite));
  if (btor->options.eliminate_slices.val)
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

  if (btor->slv) btor->slv->api.print_time_stats (btor);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (
      btor->msg, 1, "%.1f MB", btor->mm->maxallocated / (double) (1 << 20));
}

static Btor *
new_aux_btor (int init_opts)
{
  assert (init_opts == 0 || init_opts == 1);

  BtorMemMgr *mm;
  Btor *btor;

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, btor);

  btor->mm    = mm;
  btor->msg   = btor_new_btor_msg (btor->mm, &btor->options.verbosity.val);
  btor->avmgr = btor_new_aigvec_mgr (mm, btor->msg, &btor->options);

  if (init_opts) btor_init_opts (btor);

  btor->bv_assignments    = btor_new_bv_assignment_list (mm);
  btor->array_assignments = btor_new_array_assignment_list (mm);

  BTOR_INIT_UNIQUE_TABLE (mm, btor->nodes_unique_table);
  BTOR_INIT_SORT_UNIQUE_TABLE (mm, btor->sorts_unique_table);

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

  BTOR_PUSH_STACK (btor->mm, btor->nodes_id_table, 0);

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
  btor->var_rhs = btor_new_ptr_hash_table (btor->mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);

  btor->fun_rhs = btor_new_ptr_hash_table (btor->mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_INIT_STACK (btor->functions_with_model);

  btor->true_exp = btor_true_exp (btor);
  btor_set_msg_prefix_btor (btor, "btor");

  return btor;
}

Btor *
btor_new_btor (void)
{
  return new_aux_btor (1);
}

Btor *
btor_new_btor_no_init (void)
{
  return new_aux_btor (0);
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
    btor_release_sort (&btor->sorts_unique_table, sort->id);
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
  BtorPtrHashTable *t;
  BtorMemMgr *mm;
  BtorNode *exp;
  BtorHashTableIterator it, iit;

  mm = btor->mm;

  if (btor->slv) btor->slv->api.delet (btor);

  if (btor->parse_error_msg) btor_freestr (mm, btor->parse_error_msg);

  btor_delete_bv_assignment_list (
      btor->bv_assignments,
      btor->options.auto_cleanup.val
          || btor->options.auto_cleanup_internal.val);
  btor_delete_array_assignment_list (
      btor->array_assignments,
      btor->options.auto_cleanup.val
          || btor->options.auto_cleanup_internal.val);

  btor_init_node_hash_table_iterator (&it, btor->varsubst_constraints);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    btor_release_exp (btor, it.bucket->data.asPtr);
    exp = btor_next_node_hash_table_iterator (&it);
    btor_release_exp (btor, exp);
  }
  btor_delete_ptr_hash_table (btor->varsubst_constraints);

  btor_init_node_hash_table_iterator (&it, btor->inputs);
  btor_queue_node_hash_table_iterator (&it, btor->embedded_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  btor_queue_node_hash_table_iterator (&it, btor->var_rhs);
  btor_queue_node_hash_table_iterator (&it, btor->fun_rhs);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));

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
  BTOR_RELEASE_STACK (mm, btor->functions_with_model);

  BTOR_INIT_STACK (stack);
  btor_init_node_hash_table_iterator (&it, btor->lambdas);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    exp = btor_next_node_hash_table_iterator (&it);
    t   = btor_lambda_get_static_rho (exp);
    if (t)
    {
      btor_init_node_hash_table_iterator (&iit, t);
      while (btor_has_next_node_hash_table_iterator (&iit))
      {
        BTOR_PUSH_STACK (mm, stack, iit.bucket->data.asPtr);
        BTOR_PUSH_STACK (mm, stack, btor_next_node_hash_table_iterator (&iit));
      }
      btor_lambda_set_static_rho (exp, 0);
      btor_delete_ptr_hash_table (t);
    }
  }

  while (!BTOR_EMPTY_STACK (stack))
    btor_release_exp (btor, BTOR_POP_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);

  if (btor->options.auto_cleanup.val && btor->external_refs)
  {
    release_all_ext_exp_refs (btor);

    if (!btor->options.auto_cleanup_internal.val && !getenv ("BTORLEAK")
        && !getenv ("BTORLEAKEXP"))
    {
      for (i = BTOR_COUNT_STACK (btor->nodes_id_table) - 1; i >= 0; i--)
        assert (!BTOR_PEEK_STACK (btor->nodes_id_table, i));
    }
  }

  if (btor->options.auto_cleanup_internal.val)
  {
    for (i = BTOR_COUNT_STACK (btor->nodes_id_table) - 1; i >= 0; i--)
    {
      exp = BTOR_PEEK_STACK (btor->nodes_id_table, i);
      if (!exp) continue;
      if (BTOR_IS_PROXY_NODE (exp)) exp->simplified = 0;
      assert (exp->refs);
      exp->refs = 1;
      btor_release_exp (btor, exp);
      assert (!BTOR_PEEK_STACK (btor->nodes_id_table, i));
    }
  }

  if (btor->options.auto_cleanup.val && btor->external_refs)
    release_all_ext_sort_refs (btor);

  assert (btor->external_refs == 0);

#ifndef NDEBUG
  BtorNode *cur;
  if (btor->nodes_unique_table.num_elements)
    BTORLOG (1,
             "*** btor->nodes_unique_table.num_elements: %d",
             btor->nodes_unique_table.num_elements);
  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      BTORLOG (1, "  unreleased node: %s (%d)", node2string (cur), cur->refs);
#endif
  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKEXP")
          || btor->nodes_unique_table.num_elements == 0);
  BTOR_RELEASE_UNIQUE_TABLE (mm, btor->nodes_unique_table);
  BTOR_RELEASE_STACK (mm, btor->nodes_id_table);

  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKSORT")
          || btor->sorts_unique_table.num_elements == 0);
  BTOR_RELEASE_SORT_UNIQUE_TABLE (mm, btor->sorts_unique_table);

  btor_delete_ptr_hash_table (btor->node2symbol);
  btor_init_hash_table_iterator (&it, btor->symbols);
  while (btor_has_next_hash_table_iterator (&it))
    btor_freestr (btor->mm, (char *) btor_next_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (btor->symbols);

  btor_delete_ptr_hash_table (btor->bv_vars);
  btor_delete_ptr_hash_table (btor->ufs);
  btor_delete_ptr_hash_table (btor->lambdas);
  btor_delete_ptr_hash_table (btor->feqs);
  btor_delete_ptr_hash_table (btor->parameterized);

  btor_delete_aigvec_mgr (btor->avmgr);

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
static void
process_unsynthesized_constraints (Btor *btor)
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
    if (btor->options.rewrite_level.val > 2)
    {
      BtorNode *real_cur = BTOR_REAL_ADDR_NODE (cur);
      if (real_cur->kind == BTOR_BEQ_NODE)
      {
#if 0
	      BtorNode * left = real_cur->e[0];
	      BtorNode * right = real_cur->e[1];
	      BtorNode * other;

	      if (BTOR_REAL_ADDR_NODE (left)->kind == BTOR_BV_CONST_NODE)
	        other = right;
	      else if (BTOR_REAL_ADDR_NODE (right)->kind == BTOR_BV_CONST_NODE)
	        other = left;
	      else
	        other = 0;

	      // FIXME fails with symbolic lemmas (during beta-reduction
	      // rewrite level is forced to 1, hence symbolic lemmas might
	      // not be simplified as much as possible). possible solution:
	      // use rewrite level > 1 for lemma generation.
	      //if (other 
	      //    && !BTOR_IS_INVERTED_NODE (other) 
	      //    && other->kind == BTOR_ADD_NODE)
	      //  {
	      //    assert (BTOR_REAL_ADDR_NODE (
	      //  	    other->e[0])->kind != BTOR_BV_CONST_NODE);
	      //    assert (BTOR_REAL_ADDR_NODE (
	      //  	    other->e[1])->kind != BTOR_BV_CONST_NODE);
	      //  }
#endif
      }
    }
#endif

    if (!btor_find_in_ptr_hash_table (sc, cur))
    {
      aig = exp_to_aig (btor, cur);
      if (aig == BTOR_AIG_FALSE)
      {
        btor->found_constraint_false = 1;
        break;
      }
      btor_add_toplevel_aig_to_sat (amgr, aig);
      btor_release_aig (amgr, aig);
      (void) btor_insert_in_ptr_hash_table (sc, cur);
      btor_remove_from_ptr_hash_table (uc, cur, 0, 0);

      btor->stats.constraints.synthesized++;
      report_constraint_stats (btor, 0);
    }
    else
    {
      /* constraint is already in sc */
      btor_remove_from_ptr_hash_table (uc, cur, 0, 0);
      btor_release_exp (btor, cur);
    }
  }
}

static void
update_assumptions (Btor *btor)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));

  BtorPtrHashTable *ass;
  BtorNode *cur, *simp;
  BtorHashTableIterator it;

  ass = btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    if (BTOR_REAL_ADDR_NODE (cur)->simplified)
    {
      simp = btor_simplify_exp (btor, cur);
      if (!btor_find_in_ptr_hash_table (ass, simp))
        btor_insert_in_ptr_hash_table (ass, btor_copy_exp (btor, simp));
      btor_release_exp (btor, cur);
    }
    else
    {
      if (!btor_find_in_ptr_hash_table (ass, cur))
        btor_insert_in_ptr_hash_table (ass, cur);
      else
        btor_release_exp (btor, cur);
    }
  }
  btor_delete_ptr_hash_table (btor->assumptions);
  btor->assumptions = ass;
}

static void
insert_unsynthesized_constraint (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  BtorBitVector *bits;
  BtorPtrHashTable *uc;

  if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp)))
  {
    bits = btor_const_get_bits (exp);
    assert (bits->width == 1);
    if ((BTOR_IS_INVERTED_NODE (exp) && btor_get_bit_bv (bits, 0))
        || (!BTOR_IS_INVERTED_NODE (exp) && !btor_get_bit_bv (bits, 0)))
    {
      btor->inconsistent = 1;
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
  if (!btor_find_in_ptr_hash_table (uc, exp))
  {
    assert (!btor_find_in_ptr_hash_table (btor->embedded_constraints, exp));
    (void) btor_insert_in_ptr_hash_table (uc, btor_copy_exp (btor, exp));
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
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp)));

  if (!btor_find_in_ptr_hash_table (btor->embedded_constraints, exp))
  {
    assert (
        !btor_find_in_ptr_hash_table (btor->unsynthesized_constraints, exp));
    (void) btor_insert_in_ptr_hash_table (btor->embedded_constraints,
                                          btor_copy_exp (btor, exp));
    BTOR_REAL_ADDR_NODE (exp)->constraint = 1;
    btor->stats.constraints.embedded++;
  }
}

void
btor_insert_varsubst_constraint (Btor *btor, BtorNode *left, BtorNode *right)
{
  assert (btor);
  assert (left);
  assert (right);

  BtorNode *eq;
  BtorPtrHashTable *vsc;
  BtorPtrHashBucket *bucket;

  vsc    = btor->varsubst_constraints;
  bucket = btor_find_in_ptr_hash_table (vsc, left);

  if (!bucket)
  {
    BTORLOG (
        1, "add varsubst: %s -> %s", node2string (left), node2string (right));
    btor_insert_in_ptr_hash_table (vsc, btor_copy_exp (btor, left))
        ->data.asPtr = btor_copy_exp (btor, right);
    /* do not set constraint flag, as they are gone after substitution
     * and treated differently */
    btor->stats.constraints.varsubst++;
  }
  /* if v = t_1 is already in varsubst, we
   * have to synthesize v = t_2 */
  else if (right != (BtorNode *) bucket->data.asPtr)
  {
    eq = btor_eq_exp (btor, left, right);
    /* only add if it is not in a constraint table: can be already in
     * embedded or unsythesized constraints */
    if (!BTOR_REAL_ADDR_NODE (eq)->constraint)
      insert_unsynthesized_constraint (btor, eq);
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

BtorNode *
btor_aux_var_exp (Btor *btor, int len)
{
  assert (btor);
  assert (len > 0);

  BtorNode *result;
#ifndef NDEBUG
  int id = BTOR_COUNT_STACK (btor->nodes_id_table);
#endif

  result = btor_var_exp (btor, len, 0);
  assert (BTOR_IS_REGULAR_NODE (result));
  assert (result->id == id);
  return result;
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
  BTOR_INIT_QUEUE (queue);

  cur = BTOR_REAL_ADDR_NODE (right);
  goto OCCURRENCE_CHECK_ENTER_WITHOUT_POP;

  do
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_DEQUEUE (queue));
  OCCURRENCE_CHECK_ENTER_WITHOUT_POP:
    if (!btor_contains_int_hash_table (cache, cur->id))
    {
      btor_add_int_hash_table (cache, cur->id);
      if (cur == real_left)
      {
        is_cyclic = 1;
        break;
      }
      for (i = cur->arity - 1; i >= 0; i--) BTOR_ENQUEUE (mm, queue, cur->e[i]);
    }
  } while (!BTOR_EMPTY_QUEUE (queue));
  BTOR_RELEASE_QUEUE (mm, queue);
  btor_free_int_hash_table (cache);
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
  BtorNode *left, *right, *real_left, *real_right, *tmp, *inv, *var, *lambda;
  BtorNode *const_exp, *real_exp;
  int leadings;
  BtorBitVector *ic, *fc, *bits;
  BtorMemMgr *mm;
  BtorSubstCompKind comp;

  assert (btor);
  assert (exp);
  assert (left_result);
  assert (right_result);
  assert (btor->options.rewrite_level.val > 1);
  assert (btor_simplify_exp (btor, exp) == exp);

  mm = btor->mm;

  /* boolean BV_NODE, force assignment (right_result) w.r.t. phase */
  if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (exp)))
  {
    assert (btor_get_exp_width (btor, exp) == 1);
    if (BTOR_IS_INVERTED_NODE (exp))
    {
      *left_result  = btor_copy_exp (btor, BTOR_REAL_ADDR_NODE (exp));
      *right_result = btor_zero_exp (btor, 1);
    }
    else
    {
      *left_result  = btor_copy_exp (btor, exp);
      *right_result = btor_one_exp (btor, 1);
    }
    return 1;
  }

  if (BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_ULT_NODE
      && (BTOR_IS_BV_VAR_NODE (
              BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (exp)->e[0]))
          || BTOR_IS_BV_VAR_NODE (
                 BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (exp)->e[1]))))
  {
    real_exp = BTOR_REAL_ADDR_NODE (exp);

    if (BTOR_IS_INVERTED_NODE (exp))
      comp = BTOR_SUBST_COMP_UGTE_KIND;
    else
      comp = BTOR_SUBST_COMP_ULT_KIND;

    if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (real_exp->e[0])))
    {
      var   = real_exp->e[0];
      right = real_exp->e[1];
    }
    else
    {
      assert (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (real_exp->e[1])));
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
    if (btor_find_in_ptr_hash_table (btor->varsubst_constraints, var)) return 0;

    if (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (right))) return 0;

    if (BTOR_IS_INVERTED_NODE (right))
      bits = btor_not_bv (mm, btor_const_get_bits (right));
    else
      bits = btor_copy_bv (mm, btor_const_get_bits (right));

    if (comp == BTOR_SUBST_COMP_ULT_KIND || comp == BTOR_SUBST_COMP_ULTE_KIND)
    {
      leadings = btor_get_num_leading_zeros_bv (bits);
      if (leadings > 0)
      {
        const_exp = btor_zero_exp (btor, leadings);
        lambda =
            btor_aux_var_exp (btor, btor_get_exp_width (btor, var) - leadings);
        tmp = btor_concat_exp (btor, const_exp, lambda);
        btor_insert_varsubst_constraint (btor, var, tmp);
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
        const_exp = btor_ones_exp (btor, leadings);
        lambda =
            btor_aux_var_exp (btor, btor_get_exp_width (btor, var) - leadings);
        tmp = btor_concat_exp (btor, const_exp, lambda);
        btor_insert_varsubst_constraint (btor, var, tmp);
        btor_release_exp (btor, const_exp);
        btor_release_exp (btor, lambda);
        btor_release_exp (btor, tmp);
      }
    }

    btor_free_bv (btor->mm, bits);
    return 0;
  }

  /* in the boolean case a != b is the same as a == ~b */
  if (BTOR_IS_INVERTED_NODE (exp)
      && BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_BEQ_NODE
      && btor_get_exp_width (btor, BTOR_REAL_ADDR_NODE (exp)->e[0]) == 1)
  {
    left  = BTOR_REAL_ADDR_NODE (exp)->e[0];
    right = BTOR_REAL_ADDR_NODE (exp)->e[1];

    if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (left)))
    {
      *left_result  = btor_copy_exp (btor, left);
      *right_result = BTOR_INVERT_NODE (btor_copy_exp (btor, right));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }

    if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (right)))
    {
      *left_result  = btor_copy_exp (btor, right);
      *right_result = BTOR_INVERT_NODE (btor_copy_exp (btor, left));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }
  }

  if (BTOR_IS_INVERTED_NODE (exp) || !BTOR_IS_ARRAY_OR_BV_EQ_NODE (exp))
    return 0;

  left       = exp->e[0];
  right      = exp->e[1];
  real_left  = BTOR_REAL_ADDR_NODE (left);
  real_right = BTOR_REAL_ADDR_NODE (right);

  if (!BTOR_IS_BV_VAR_NODE (real_left) && !BTOR_IS_BV_VAR_NODE (real_right)
      && !BTOR_IS_UF_NODE (real_left) && !BTOR_IS_UF_NODE (real_right))
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
    if ((!BTOR_IS_BV_VAR_NODE (real_left) && BTOR_IS_BV_VAR_NODE (real_right))
        || (!BTOR_IS_UF_NODE (real_left) && BTOR_IS_UF_NODE (real_right)))
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
  assert (btor->options.rewrite_level.val > 1);
  assert (btor_get_exp_width (btor, exp) == 1);

  BtorNode *rep;

  rep = btor_simplify_exp (btor, exp);

  return rep == BTOR_INVERT_NODE (rep)
         /* special case: top-level constraint applies are not simplified to
          * true/false (in order to not break dual prop) */
         || btor_find_in_ptr_hash_table (btor->synthesized_constraints,
                                         BTOR_INVERT_NODE (rep))
         || btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                         BTOR_INVERT_NODE (rep))
         || btor_find_in_ptr_hash_table (btor->embedded_constraints,
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

  if (BTOR_IS_BV_CONST_NODE (real_exp))
  {
    bits = btor_const_get_bits (real_exp);
    assert (bits->width == 1);
    /* we do not add true/false */
    if ((BTOR_IS_INVERTED_NODE (exp) && btor_get_bit_bv (bits, 0))
        || (!BTOR_IS_INVERTED_NODE (exp) && !btor_get_bit_bv (bits, 0)))
      btor->inconsistent = 1;
    else
    {
      assert ((BTOR_IS_INVERTED_NODE (exp) && !btor_get_bit_bv (bits, 0))
              || (!BTOR_IS_INVERTED_NODE (exp) && btor_get_bit_bv (bits, 0)));
    }
    return;
  }

  if (!btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp))
  {
    if (btor->options.rewrite_level.val > 1)
    {
      if (normalize_substitution (btor, exp, &left, &right))
      {
        btor_insert_varsubst_constraint (btor, left, right);
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
        btor->inconsistent = 1;
      else
      {
        if (!real_exp->constraint)
        {
          if (is_embedded_constraint_exp (btor, exp))
            insert_embedded_constraint (btor, exp);
          else
            insert_unsynthesized_constraint (btor, exp);
        }
        else
        {
          assert (
              btor_find_in_ptr_hash_table (btor->unsynthesized_constraints, exp)
              || btor_find_in_ptr_hash_table (btor->embedded_constraints, exp));
        }
      }
    }
    else
      insert_unsynthesized_constraint (btor, exp);

    report_constraint_stats (btor, 0);
  }
}

void
btor_reset_assumptions (Btor *btor)
{
  assert (btor);

  BtorHashTableIterator it;

  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
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
    if (!BTOR_IS_PROXY_NODE (cur))
    {
      assert (BTOR_IS_FUN_NODE (cur));
      assert (cur->rho);
      btor_delete_ptr_hash_table (cur->rho);
      cur->rho = 0;
    }
    btor_release_exp (btor, cur);
  }
  BTOR_RESET_STACK (btor->functions_with_model);
}

static void
reset_incremental_usage (Btor *btor)
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
  assert (check_id_table_mark_unset_dbg (btor));

  BtorNode *cur, *child;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;

  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (btor_get_exp_width (btor, exp) == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  mm = btor->mm;
  if (btor->valid_assignments) reset_incremental_usage (btor);

  if (!BTOR_IS_INVERTED_NODE (exp) && BTOR_IS_AND_NODE (exp))
  {
    BTOR_INIT_STACK (stack);
    cur = exp;
    goto ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP:
      assert (!BTOR_IS_INVERTED_NODE (cur));
      assert (BTOR_IS_AND_NODE (cur));
      assert (cur->mark == 0 || cur->mark == 1);
      if (!cur->mark)
      {
        cur->mark = 1;
        child     = cur->e[1];
        if (!BTOR_IS_INVERTED_NODE (child) && BTOR_IS_AND_NODE (child))
          BTOR_PUSH_STACK (mm, stack, child);
        else
          insert_new_constraint (btor, child);
        child = cur->e[0];
        if (!BTOR_IS_INVERTED_NODE (child) && BTOR_IS_AND_NODE (child))
          BTOR_PUSH_STACK (mm, stack, child);
        else
          insert_new_constraint (btor, child);
      }
    } while (!BTOR_EMPTY_STACK (stack));
    BTOR_RELEASE_STACK (mm, stack);
    mark_exp (btor, exp, 0);
  }
  else
    insert_new_constraint (btor, exp);

  assert (check_constraints_not_const_dbg (btor));
}

void
btor_assert_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
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

  if (BTOR_IS_CONST_AIG (aig))
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
  assert (btor->options.incremental.val);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  /* Note: do not simplify constraint expression in order to prevent
   *       constraint expressions from not being added to btor->assumptions. */
  if (BTOR_REAL_ADDR_NODE (exp)->simplified)
    exp = btor_simplify_exp (btor, exp);

  if (btor->valid_assignments) reset_incremental_usage (btor);

  if (!btor_find_in_ptr_hash_table (btor->assumptions, exp))
    (void) btor_insert_in_ptr_hash_table (btor->assumptions,
                                          btor_copy_exp (btor, exp));
}

int
btor_is_assumption_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor->options.incremental.val);
  assert (exp);
  assert (check_id_table_mark_unset_dbg (btor));

  exp = btor_simplify_exp (btor, exp);

  if (BTOR_REAL_ADDR_NODE (exp) == BTOR_REAL_ADDR_NODE (btor->true_exp))
    return 1;

  if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp))
      || btor_get_exp_width (btor, exp) != 1
      || BTOR_REAL_ADDR_NODE (exp)->parameterized)
    return 0;

  return btor_find_in_ptr_hash_table (btor->assumptions, exp) ? 1 : 0;
}

int
btor_failed_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor->options.incremental.val);
  assert (btor->last_sat_result == BTOR_UNSAT);
  assert (exp);
  assert (check_id_table_mark_unset_dbg (btor));

  int i, lit, res;
  double start;
  BtorAIG *aig;
  BtorNode *real_exp, *cur, *e;
  BtorNodePtrStack work_stack, assumptions;
  BtorSATMgr *smgr;

  start = btor_time_stamp ();

  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->btor == btor);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (btor_get_exp_width (btor, exp) == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);
  assert (btor_is_assumption_exp (btor, exp));

  if (btor->inconsistent)
  {
    res = 0;
  }
  else if (exp == btor->true_exp)
  {
    res = 0;
  }
  else if (exp == BTOR_INVERT_NODE (btor->true_exp))
  {
    res = 1;
  }
  else if (BTOR_IS_INVERTED_NODE (exp) || !BTOR_IS_AND_NODE (exp))
  {
    real_exp = BTOR_REAL_ADDR_NODE (exp);
    assert (btor->found_constraint_false || BTOR_IS_SYNTH_NODE (real_exp));

    if (!BTOR_IS_SYNTH_NODE (real_exp))
    {
      res = 0;
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
        res = 0;
      }
      else
      {
        smgr = btor_get_sat_mgr_btor (btor);
        lit  = exp_to_cnf_lit (btor, exp);
        if (abs (lit) == smgr->true_lit)
          res = lit < 0 ? 1 : 0;
        else
          res = btor_failed_sat (smgr, lit);
      }
    }
  }
  else
  {
    res = 0;
    BTOR_INIT_STACK (assumptions);
    BTOR_INIT_STACK (work_stack);
    BTOR_PUSH_STACK (btor->mm, work_stack, exp);
    while (!BTOR_EMPTY_STACK (work_stack))
    {
      cur = BTOR_POP_STACK (work_stack);
      assert (!BTOR_IS_INVERTED_NODE (cur));
      assert (BTOR_IS_AND_NODE (cur));
      assert (cur->mark == 0 || cur->mark == 1);
      if (cur->mark) continue;
      cur->mark = 1;
      for (i = 0; i < 2; i++)
      {
        e = cur->e[i];
        if (!BTOR_IS_INVERTED_NODE (e) && BTOR_IS_AND_NODE (e))
          BTOR_PUSH_STACK (btor->mm, work_stack, e);
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
          BTOR_PUSH_STACK (btor->mm, assumptions, e);
        }
      }
    }

    smgr = btor_get_sat_mgr_btor (btor);
    while (!BTOR_EMPTY_STACK (assumptions))
    {
      cur = BTOR_POP_STACK (assumptions);
      assert (BTOR_IS_INVERTED_NODE (cur) || !BTOR_IS_AND_NODE (cur));
      lit = exp_to_cnf_lit (btor, cur);
      if (lit == smgr->true_lit) continue;
      if (lit == -smgr->true_lit) goto ASSUMPTION_FAILED;
      if (btor_failed_sat (smgr, lit))
      {
      ASSUMPTION_FAILED:
        BTOR_RELEASE_STACK (btor->mm, work_stack);
        BTOR_RELEASE_STACK (btor->mm, assumptions);
        mark_exp (btor, exp, 0);
        res = 1;
      }
    }
    BTOR_RELEASE_STACK (btor->mm, work_stack);
    BTOR_RELEASE_STACK (btor->mm, assumptions);
    mark_exp (btor, exp, 0);
  }

  btor->time.failed += btor_time_stamp () - start;

  return res;
}

void
btor_fixate_assumptions (Btor *btor)
{
  BtorHashTableIterator it;
  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_assert_exp (btor, btor_next_node_hash_table_iterator (&it));
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

  if (btor_find_in_ptr_hash_table (unsynthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = unsynthesized_constraints;
  }

  if (btor_find_in_ptr_hash_table (unsynthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = unsynthesized_constraints;
  }

  if (btor_find_in_ptr_hash_table (embedded_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = embedded_constraints;
  }

  if (btor_find_in_ptr_hash_table (embedded_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = embedded_constraints;
  }

  if (btor_find_in_ptr_hash_table (synthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = synthesized_constraints;
  }

  if (btor_find_in_ptr_hash_table (synthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = synthesized_constraints;
  }

  if (pos)
  {
    btor_remove_from_ptr_hash_table (pos, exp, 0, 0);
    btor_release_exp (btor, exp);
  }

  if (neg)
  {
    btor_remove_from_ptr_hash_table (neg, not_exp, 0, 0);
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
  assert (exp->sort_id == BTOR_REAL_ADDR_NODE (simplified)->sort_id);
  assert (exp->parameterized
          || !BTOR_REAL_ADDR_NODE (simplified)->parameterized);
  assert (!BTOR_REAL_ADDR_NODE (simplified)->parameterized
          || exp->parameterized);

  if (exp->simplified) btor_release_exp (btor, exp->simplified);

  exp->simplified = btor_copy_exp (btor, simplified);

  if (exp->constraint) update_constraints (btor, exp);

  /* if a variable or UF gets simplified we need to save the original input
   * exp in a hash table (for model generation) */
  if (BTOR_IS_BV_VAR_NODE (exp)
      && !btor_find_in_ptr_hash_table (btor->var_rhs, exp))
  {
    btor_insert_in_ptr_hash_table (btor->var_rhs, btor_copy_exp (btor, exp));
  }
  else if (BTOR_IS_UF_NODE (exp)
           && !btor_find_in_ptr_hash_table (btor->fun_rhs, exp))
  {
    btor_insert_in_ptr_hash_table (btor->fun_rhs, btor_copy_exp (btor, exp));
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
    assert (BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (simplified)));
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
  assert (btor->options.rewrite_level.val > 1);

  BtorNode *real_exp, *result, *not_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  /* Do not simplify top-level constraint applies (we need the implication
   * dependencies for determining top applies when dual prop enabled) */
  if (btor->options.dual_prop.val && BTOR_IS_APPLY_NODE (real_exp)) return exp;

  not_exp = BTOR_INVERT_NODE (real_exp);

  if (BTOR_IS_BV_CONST_NODE (real_exp)) return exp;

  if (btor_find_in_ptr_hash_table (btor->embedded_constraints, real_exp))
  {
    result = btor->true_exp;
  }
  else if (btor_find_in_ptr_hash_table (btor->embedded_constraints, not_exp))
  {
    result = BTOR_INVERT_NODE (btor->true_exp);
  }
  else if (btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                        real_exp))
  {
    result = btor->true_exp;
  }
  else if (btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                        not_exp))
  {
    result = BTOR_INVERT_NODE (btor->true_exp);
  }
  else if (btor_find_in_ptr_hash_table (btor->synthesized_constraints,
                                        real_exp))
  {
    result = btor->true_exp;
  }
  else
  {
    assert (
        btor_find_in_ptr_hash_table (btor->synthesized_constraints, not_exp));
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
  if (btor->options.simplify_constraints.val
      && btor->options.rewrite_level.val > 1
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
  BtorHashTableIterator it, iit;
  BtorPtrHashTable *static_rho, *new_static_rho;

  /* update static_rhos */
  btor_init_node_hash_table_iterator (&it, btor->lambdas);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur        = btor_next_node_hash_table_iterator (&it);
    static_rho = btor_lambda_get_static_rho (cur);

    if (!static_rho) continue;

    new_static_rho = btor_new_ptr_hash_table (btor->mm, 0, 0);
    /* update static rho to get rid of proxy nodes */
    btor_init_node_hash_table_iterator (&iit, static_rho);
    while (btor_has_next_node_hash_table_iterator (&iit))
    {
      data = iit.bucket->data.asPtr;
      key  = btor_next_node_hash_table_iterator (&iit);
      assert (BTOR_IS_REGULAR_NODE (key));
      simp_key  = btor_simplify_exp (btor, key);
      simp_data = btor_simplify_exp (btor, data);

      if (!btor_find_in_ptr_hash_table (new_static_rho, simp_key))
      {
        btor_insert_in_ptr_hash_table (new_static_rho,
                                       btor_copy_exp (btor, simp_key))
            ->data.asPtr = btor_copy_exp (btor, simp_data);
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
  assert (BTOR_IS_LAMBDA_NODE (exp));
  assert (!btor_param_cur_assignment (exp->e[0]));

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
    case BTOR_AND_NODE: return btor_and_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_BEQ_NODE:
    case BTOR_FEQ_NODE: return btor_eq_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ADD_NODE: return btor_add_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_MUL_NODE: return btor_mul_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ULT_NODE: return btor_ult_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SLL_NODE: return btor_sll_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SRL_NODE: return btor_srl_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UDIV_NODE: return btor_udiv_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UREM_NODE: return btor_urem_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_CONCAT_NODE: return btor_concat_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_LAMBDA_NODE: return rebuild_lambda_exp (btor, exp);
    case BTOR_APPLY_NODE: return btor_apply_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ARGS_NODE: return btor_args_exp (btor, exp->arity, exp->e);
    default:
      assert (BTOR_IS_COND_NODE (exp));
      return btor_cond_exp (btor, exp->e[0], exp->e[1], exp->e[2]);
  }
}

/* we perform all variable substitutions in one pass and rebuild the formula
 * cyclic substitutions must have been deleted before! */
static void
substitute_vars_and_rebuild_exps (Btor *btor, BtorPtrHashTable *substs)
{
  assert (btor);
  assert (substs);
  assert (check_id_table_aux_mark_unset_dbg (btor));

  BtorNodePtrStack stack, root_stack;
  BtorPtrHashBucket *b;
  BtorNode *cur, *cur_parent, *rebuilt_exp, **temp, **top, *rhs, *simplified;
  BtorMemMgr *mm;
  BtorHashTableIterator it;
  BtorNodeIterator nit;
  int pushed, i;

  if (substs->count == 0u) return;

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (root_stack);
  /* search upwards for all reachable roots */
  /* we push all left sides on the search stack */
  btor_init_node_hash_table_iterator (&it, substs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_UF_NODE (cur));
    BTOR_PUSH_STACK (mm, stack, cur);
  }

  do
  {
    assert (!BTOR_EMPTY_STACK (stack));
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->aux_mark == 0)
    {
      cur->aux_mark = 1;
      btor_init_parent_iterator (&nit, cur);
      /* are we at a root ? */
      pushed = 0;
      while (btor_has_next_parent_iterator (&nit))
      {
        cur_parent = btor_next_parent_iterator (&nit);
        assert (BTOR_IS_REGULAR_NODE (cur_parent));
        pushed = 1;
        BTOR_PUSH_STACK (mm, stack, cur_parent);
      }
      if (!pushed) BTOR_PUSH_STACK (mm, root_stack, btor_copy_exp (btor, cur));
    }
  } while (!BTOR_EMPTY_STACK (stack));

  /* copy roots on substitution stack */
  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    BTOR_PUSH_STACK (mm, stack, *temp);

  /* substitute */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

    if (cur->aux_mark == 0) continue;

    assert (!BTOR_IS_BV_CONST_NODE (cur));

    if (cur->aux_mark == 1)
    {
      BTOR_PUSH_STACK (mm, stack, cur);
      cur->aux_mark = 2;
      if (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_UF_NODE (cur))
      {
        b = btor_find_in_ptr_hash_table (substs, cur);
        assert (b);
        assert (cur == (BtorNode *) b->key);
        rhs = (BtorNode *) b->data.asPtr;
        assert (rhs);
        BTOR_PUSH_STACK (mm, stack, rhs);
      }
      else
      {
        for (i = cur->arity - 1; i >= 0; i--)
          BTOR_PUSH_STACK (mm, stack, cur->e[i]);
      }
    }
    else
    {
      assert (cur->aux_mark == 2);
      cur->aux_mark = 0;
      if (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_UF_NODE (cur))
      {
        b = btor_find_in_ptr_hash_table (substs, cur);
        assert (b);
        assert (cur == (BtorNode *) b->key);
        rhs = (BtorNode *) b->data.asPtr;
        assert (rhs);
        rebuilt_exp = btor_copy_exp (btor, rhs);
        if (BTOR_IS_BV_VAR_NODE (cur))
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

  BTOR_RELEASE_STACK (mm, stack);

  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    btor_release_exp (btor, *temp);
  BTOR_RELEASE_STACK (mm, root_stack);

  update_node_hash_tables (btor);
  assert (check_lambdas_static_rho_proxy_free_dbg (btor));
}

static void
substitute_var_exps (Btor *btor)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));

  BtorPtrHashTable *varsubst_constraints, *order, *substs;
  BtorNode *cur, *constraint, *left, *right, *child;
  BtorPtrHashBucket *b, *b_temp;
  BtorHashTableIterator it;
  int order_num, val, max, i;
  BtorNodePtrStack stack;
  double start, delta;
  unsigned count;
  BtorMemMgr *mm;

  mm                   = btor->mm;
  varsubst_constraints = btor->varsubst_constraints;

  if (varsubst_constraints->count == 0u) return;

  start = btor_time_stamp ();

  BTOR_INIT_STACK (stack);

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
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_UF_NODE (cur));
      right = (BtorNode *) b->data.asPtr;
      /* NOTE: we need to update 'right' here, since 'right' might have
       * already been rebuilt in merge_lambdas (in beta reduction part) */
      btor_insert_in_ptr_hash_table (substs, cur)->data.asPtr =
          btor_copy_exp (btor, btor_simplify_exp (btor, right));
      btor_release_exp (btor, right);
      btor_remove_from_ptr_hash_table (varsubst_constraints, cur, 0, 0);
    }
    assert (varsubst_constraints->count == 0u);

    /* we search for cyclic substitution dependencies
     * and map the substitutions to an ordering number */
    btor_init_node_hash_table_iterator (&it, substs);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_UF_NODE (cur));
      BTOR_PUSH_STACK (mm, stack, (BtorNode *) cur);

      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

        if (!cur)
        {
          cur = BTOR_POP_STACK (stack); /* left */
          assert (BTOR_IS_REGULAR_NODE (cur));
          assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_UF_NODE (cur));
          assert (!btor_find_in_ptr_hash_table (order, cur));
          btor_insert_in_ptr_hash_table (order, cur)->data.asInt = order_num++;
          continue;
        }

        if (cur->mark == 1) /* visited (DFS) */
          continue;

        cur->mark = 1;

        if (BTOR_IS_BV_CONST_NODE (cur) || BTOR_IS_BV_VAR_NODE (cur)
            || BTOR_IS_PARAM_NODE (cur) || BTOR_IS_UF_NODE (cur))
        {
          b_temp = btor_find_in_ptr_hash_table (substs, cur);
          if (b_temp)
          {
            BTOR_PUSH_STACK (mm, stack, cur); /* left  */
            BTOR_PUSH_STACK (mm, stack, 0);
            BTOR_PUSH_STACK (mm,
                             stack, /* right */
                             (BtorNode *) b_temp->data.asPtr);
          }
          else
          {
            assert (!btor_find_in_ptr_hash_table (order, cur));
            btor_insert_in_ptr_hash_table (order, cur)->data.asInt = 0;
          }
        }
        else
        {
          assert (cur->arity >= 1);
          assert (cur->arity <= 3);
          for (i = cur->arity - 1; i >= 0; i--)
            BTOR_PUSH_STACK (mm, stack, cur->e[i]);
        }
      }
    }

    /* intermediate cleanup of mark flags */
    btor_init_node_hash_table_iterator (&it, substs);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      b   = it.bucket;
      cur = btor_next_node_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_UF_NODE (cur));
      mark_exp (btor, cur, 0);
      mark_exp (btor, (BtorNode *) b->data.asPtr, 0);
    }

    /* we look for cycles */
    btor_init_node_hash_table_iterator (&it, substs);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      b   = it.bucket;
      cur = btor_next_node_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_UF_NODE (cur));
      BTOR_PUSH_STACK (mm, stack, (BtorNode *) b->data.asPtr);

      /* we assume that there are no direct loops
       * as a result of occurrence check */
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

        if (cur->mark == 2) /* cur has max order of its children */
          continue;

        if (BTOR_IS_BV_CONST_NODE (cur) || BTOR_IS_BV_VAR_NODE (cur)
            || BTOR_IS_PARAM_NODE (cur) || BTOR_IS_UF_NODE (cur))
        {
          assert (btor_find_in_ptr_hash_table (order, cur));
          continue;
        }

        assert (cur->arity >= 1);
        assert (cur->arity <= 3);

        if (cur->mark == 0)
        {
          cur->mark = 1;
          BTOR_PUSH_STACK (mm, stack, cur);
          for (i = cur->arity - 1; i >= 0; i--)
            BTOR_PUSH_STACK (mm, stack, cur->e[i]);
        }
        else /* cur is visited, its children are visited */
        {
          /* compute maximum of children */
          assert (cur->mark == 1);
          cur->mark = 2;
          max       = 0;
          for (i = cur->arity - 1; i >= 0; i--)
          {
            child  = BTOR_REAL_ADDR_NODE (cur->e[i]);
            b_temp = btor_find_in_ptr_hash_table (order, child);
            assert (b_temp);
            val = b_temp->data.asInt;
            assert (val >= 0);
            max = BTOR_MAX_UTIL (max, val);
          }
          btor_insert_in_ptr_hash_table (order, cur)->data.asInt = max;
        }
      }
    }

    assert (BTOR_EMPTY_STACK (stack));
    /* we eliminate cyclic substitutions, and reset mark flags */
    btor_init_node_hash_table_iterator (&it, substs);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      right = (BtorNode *) it.bucket->data.asPtr;
      assert (right);
      left = btor_next_node_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (BTOR_IS_BV_VAR_NODE (left) || BTOR_IS_UF_NODE (left));
      mark_exp (btor, left, 0);
      mark_exp (btor, right, 0);
      b_temp = btor_find_in_ptr_hash_table (order, left);
      assert (b_temp);
      order_num = b_temp->data.asInt;
      b_temp = btor_find_in_ptr_hash_table (order, BTOR_REAL_ADDR_NODE (right));
      assert (b_temp);
      max = b_temp->data.asInt;
      assert (order_num != max);
      /* found cycle */
      if (max > order_num) BTOR_PUSH_STACK (mm, stack, left);
    }

    /* we delete cyclic substitutions and synthesize them instead */
    while (!BTOR_EMPTY_STACK (stack))
    {
      left = BTOR_POP_STACK (stack);
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (BTOR_IS_BV_VAR_NODE (left) || BTOR_IS_UF_NODE (left));
      right =
          (BtorNode *) btor_find_in_ptr_hash_table (substs, left)->data.asPtr;
      assert (right);

      constraint = btor_eq_exp (btor, left, right);
      /* only add if it is not in a constraint table: can be already in
       * embedded or unsythesized constraints */
      if (!BTOR_REAL_ADDR_NODE (constraint)->constraint)
        insert_unsynthesized_constraint (btor, constraint);
      btor_release_exp (btor, constraint);

      btor_remove_from_ptr_hash_table (substs, left, 0, 0);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    /* we rebuild and substiute variables in one pass */
    substitute_vars_and_rebuild_exps (btor, substs);

    /* cleanup, we delete all substitution constraints */
    btor_init_node_hash_table_iterator (&it, substs);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      right = (BtorNode *) it.bucket->data.asPtr;
      assert (right);
      left = btor_next_node_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (left->kind == BTOR_PROXY_NODE);
      assert (left->simplified);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    btor_delete_ptr_hash_table (order);
    btor_delete_ptr_hash_table (substs);
  }

  BTOR_RELEASE_STACK (mm, stack);
  delta = btor_time_stamp () - start;
  btor->time.subst += delta;
  BTOR_MSG (
      btor->msg, 1, "%d variables substituted in %.1f seconds", count, delta);
}

static int
all_exps_below_rebuilt (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int i;
  BtorNode *subst;

  subst = btor_find_substitution (btor, exp);
  if (subst)
  {
    subst = btor_simplify_exp (btor, subst);
    return BTOR_REAL_ADDR_NODE (subst)->aux_mark == 0;
  }

  exp = BTOR_REAL_ADDR_NODE (exp);
  for (i = 0; i < exp->arity; i++)
    if (BTOR_REAL_ADDR_NODE (exp->e[i])->aux_mark > 0) return 0;

  return 1;
}

/* beta reduction parameter 'bra'
 * -1 ... full beta reduction
 *  0 ... no beta reduction
 * >0 ... bound for bounded beta reduction
 */
static void
substitute_and_rebuild (Btor *btor, BtorPtrHashTable *subst, int bra)
{
  assert (btor);
  assert (subst);
  assert (check_id_table_aux_mark_unset_dbg (btor));

  int i;
  double start;
  BtorMemMgr *mm;
  BtorNode *cur, *cur_parent, *rebuilt_exp, *simplified, *sub;
  BtorNodePtrStack roots;
  BtorNodePtrQueue queue;
  BtorHashTableIterator hit;
  BtorNodeIterator it;

  if (subst->count == 0u) return;

  start = btor_time_stamp ();
  mm    = btor->mm;

  BTOR_INIT_STACK (roots);
  BTOR_INIT_QUEUE (queue);

  btor_init_node_hash_table_iterator (&hit, subst);
  while (btor_has_next_node_hash_table_iterator (&hit))
  {
    cur = BTOR_REAL_ADDR_NODE (btor_next_node_hash_table_iterator (&hit));
    BTOR_ENQUEUE (mm, queue, cur);
  }

  /* mark cone and copy roots */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!BTOR_IS_PROXY_NODE (cur));

    if (cur->aux_mark == 0)
    {
      cur->aux_mark = 1;

      if (cur->parents == 0)
        BTOR_PUSH_STACK (mm, roots, btor_copy_exp (btor, cur));

      btor_init_parent_iterator (&it, cur);
      while (btor_has_next_parent_iterator (&it))
      {
        cur_parent = btor_next_parent_iterator (&it);
        BTOR_ENQUEUE (mm, queue, cur_parent);
      }
    }
  }

  btor_init_node_hash_table_iterator (&hit, subst);
  while (btor_has_next_node_hash_table_iterator (&hit))
  {
    cur = BTOR_REAL_ADDR_NODE (btor_next_node_hash_table_iterator (&hit));
    assert (cur->aux_mark == 1);
    BTOR_ENQUEUE (mm, queue, btor_copy_exp (btor, cur));
    cur->aux_mark = 2; /* mark as enqueued */
  }

  /* rebuild bottom-up */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!BTOR_IS_PROXY_NODE (cur));
    assert (cur->aux_mark == 2);

    if (cur->refs == 1)
    {
      btor_release_exp (btor, cur);
      continue;
    }

    if (all_exps_below_rebuilt (btor, cur))
    {
      cur->aux_mark = 0;
      btor_release_exp (btor, cur);

      /* traverse upwards and enqueue all parents that are not yet
       * in the queue. */
      btor_init_parent_iterator (&it, cur);
      while (btor_has_next_parent_iterator (&it))
      {
        cur_parent = btor_next_parent_iterator (&it);
        if (cur_parent->aux_mark == 2
            || !all_exps_below_rebuilt (btor, cur_parent))
          continue;
        assert (cur_parent->aux_mark == 0 || cur_parent->aux_mark == 1);
        cur_parent->aux_mark = 2;
        BTOR_ENQUEUE (mm, queue, btor_copy_exp (btor, cur_parent));
      }

      if ((sub = btor_find_substitution (btor, cur)))
      {
        rebuilt_exp = btor_copy_exp (btor, sub);
      }
      // TODO: externalize
      else if (bra && BTOR_IS_APPLY_NODE (cur)
               && btor_find_in_ptr_hash_table (subst, cur))
      {
        if (bra == -1)
          rebuilt_exp = btor_beta_reduce_full (btor, cur);
        else
          rebuilt_exp = btor_beta_reduce_bounded (btor, cur, bra);
      }
      else
        rebuilt_exp = rebuild_exp (btor, cur);

      assert (BTOR_REAL_ADDR_NODE (cur)->sort_id
              == BTOR_REAL_ADDR_NODE (rebuilt_exp)->sort_id);
      assert (rebuilt_exp);
      if (rebuilt_exp != cur)
      {
        simplified = btor_simplify_exp (btor, rebuilt_exp);
        // TODO: only push new roots? use hash table for roots instead of
        // stack?
        if (cur->parents == 0)
          BTOR_PUSH_STACK (mm, roots, btor_copy_exp (btor, cur));

        set_simplified_exp (btor, cur, simplified);
      }
      btor_release_exp (btor, rebuilt_exp);
    }
    /* not all children rebuilt, enqueue again */
    else
    {
      assert (cur->aux_mark == 2);
      BTOR_ENQUEUE (mm, queue, cur);
    }
  }

  BTOR_RELEASE_QUEUE (mm, queue);

  for (i = 0; i < BTOR_COUNT_STACK (roots); i++)
  {
    cur = BTOR_PEEK_STACK (roots, i);
    btor_release_exp (btor, cur);
  }

  BTOR_RELEASE_STACK (mm, roots);

  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (check_unique_table_children_proxy_free_dbg (btor));

  update_node_hash_tables (btor);
  assert (check_lambdas_static_rho_proxy_free_dbg (btor));
  btor->time.subst_rebuild += btor_time_stamp () - start;
}

void
btor_substitute_and_rebuild (Btor *btor, BtorPtrHashTable *substs, int bra)
{
  substitute_and_rebuild (btor, substs, bra);
}

static void
substitute_embedded_constraints (Btor *btor)
{
  assert (btor);

  BtorHashTableIterator it;
  BtorNode *cur;

  btor_init_node_hash_table_iterator (&it, btor->embedded_constraints);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_REAL_ADDR_NODE (cur)->constraint);
    /* embedded constraints have possibly lost their parents,
     * e.g. top conjunction of constraints that are released */
    if (BTOR_REAL_ADDR_NODE (cur)->parents > 0) btor->stats.ec_substitutions++;
  }

  substitute_and_rebuild (btor, btor->embedded_constraints, 0);
}

static void
process_embedded_constraints (Btor *btor)
{
  assert (btor);

  BtorHashTableIterator it;
  BtorNodePtrStack ec;
  double start, delta;
  BtorNode *cur;
  int count;

  if (btor->embedded_constraints->count > 0u)
  {
    start = btor_time_stamp ();
    count = 0;
    BTOR_INIT_STACK (ec);
    btor_init_node_hash_table_iterator (&it, btor->embedded_constraints);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_copy_exp (btor, btor_next_node_hash_table_iterator (&it));
      BTOR_PUSH_STACK (btor->mm, ec, cur);
    }

    /* Note: it may happen that new embedded constraints are inserted into
     *       btor->embedded_constraints here. */
    substitute_embedded_constraints (btor);

    while (!BTOR_EMPTY_STACK (ec))
    {
      cur = BTOR_POP_STACK (ec);

      if (btor_find_in_ptr_hash_table (btor->embedded_constraints, cur))
      {
        count++;
        btor_remove_from_ptr_hash_table (btor->embedded_constraints, cur, 0, 0);
        insert_unsynthesized_constraint (btor, cur);
        btor_release_exp (btor, cur);
      }
      btor_release_exp (btor, cur);
    }
    BTOR_RELEASE_STACK (btor->mm, ec);

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
init_cache (Btor *btor)
{
  assert (btor);
  assert (!btor->cache);

  btor->cache = btor_new_ptr_hash_table (
      btor->mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
}

static void
release_cache (Btor *btor)
{
  assert (btor);
  assert (btor->cache);

  BtorNodePair *pair;
  BtorHashTableIterator it;

  btor_init_hash_table_iterator (&it, btor->cache);
  while (btor_has_next_hash_table_iterator (&it))
  {
    btor_release_exp (btor, (BtorNode *) it.bucket->data.asPtr);
    pair = btor_next_hash_table_iterator (&it);
    delete_exp_pair (btor, pair);
  }
  btor_delete_ptr_hash_table (btor->cache);
  btor->cache = 0;
}

int
btor_simplify (Btor *btor)
{
  assert (btor);

  int rounds, result;
  double start, delta;
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  int skelrounds = 0;
#endif

  rounds = 0;
  start  = btor_time_stamp ();

  if (btor->inconsistent) goto DONE;

  if (btor->options.beta_reduce_all.val) init_cache (btor);

  do
  {
    rounds++;
    assert (check_all_hash_tables_proxy_free_dbg (btor));
    assert (check_all_hash_tables_simp_free_dbg (btor));
    assert (check_unique_table_children_proxy_free_dbg (btor));
    if (btor->options.rewrite_level.val > 1)
    {
      substitute_var_exps (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));

      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count)
        break;  // TODO (ma): continue instead of break?

      process_embedded_constraints (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));

      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) continue;
    }

    if (btor->options.eliminate_slices.val
        && btor->options.rewrite_level.val > 2
        && !btor->options.incremental.val)
    {
      btor_eliminate_slices_on_bv_vars (btor);
      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count
          || btor->embedded_constraints->count)
        continue;
    }

#ifndef BTOR_DO_NOT_PROCESS_SKELETON
    if (btor->options.rewrite_level.val > 2
        && btor->options.skeleton_preproc.val)
    {
      skelrounds++;
      if (skelrounds <= 1)  // TODO only one?
      {
        btor_process_skeleton (btor);
        assert (check_all_hash_tables_proxy_free_dbg (btor));
        assert (check_all_hash_tables_simp_free_dbg (btor));
        assert (check_unique_table_children_proxy_free_dbg (btor));
        if (btor->inconsistent) break;
      }

      if (btor->varsubst_constraints->count
          || btor->embedded_constraints->count)
        continue;
    }
#endif

    if (btor->options.rewrite_level.val > 2
        /* FIXME: extraction not supported yet for extensional lambdas */
        && btor->feqs->count == 0
        /* FIXME: merging not supported yet for incremental due to
         * extensionality*/
        && !btor->options.incremental.val && !btor->options.beta_reduce_all.val
        && btor->options.extract_lambdas.val)
      btor_extract_lambdas (btor);

    if (btor->options.rewrite_level.val > 2
        /* merging lambdas not required if they get eliminated */
        && !btor->options.beta_reduce_all.val
        && btor->options.merge_lambdas.val)
      btor_merge_lambdas (btor);

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
    if (btor->options.ucopt.val && btor->options.rewrite_level.val > 2
        && !btor->options.incremental.val && !btor->options.model_gen.val)
    {
      btor_optimize_unconstrained (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));
      if (btor->inconsistent) break;
    }
#endif

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    /* rewrite/beta-reduce applies on lambdas */
    if (btor->options.beta_reduce_all.val)
      //	  /* FIXME: full beta reduction may produce lambdas that do not
      // have a
      //	   * static_rho */
      //	  && btor->feqs->count == 0)
      btor_eliminate_applies (btor);

    /* add ackermann constraints for all uninterpreted functions */
    if (btor->options.ackermannize.val) btor_add_ackermann_constraints (btor);
  } while (btor->varsubst_constraints->count
           || btor->embedded_constraints->count);

  if (btor->options.beta_reduce_all.val) release_cache (btor);

DONE:
  delta = btor_time_stamp () - start;
  btor->time.rewrite += delta;
  BTOR_MSG (btor->msg, 1, "%d rewriting rounds in %.1f seconds", rounds, delta);

  if (btor->inconsistent)
    result = BTOR_UNSAT;
  else if (btor->unsynthesized_constraints->count == 0u
           && btor->synthesized_constraints->count == 0u)
    result = BTOR_SAT;
  else
    result = BTOR_UNKNOWN;

  BTOR_MSG (btor->msg, 1, "simplification returned %d", result);
  return result;
}

/* bit vector skeleton is always encoded, i.e., if BTOR_IS_SYNTH_NODE is true,
 * then it is also encoded. with option lazy_synthesize enabled,
 * 'synthesize_exp' stops at feq and apply nodes */
static void
synthesize_exp (Btor *btor, BtorNode *exp, BtorPtrHashTable *backannotation)
{
  BtorNodePtrStack exp_stack;
  BtorNode *cur, *value, *args;
  BtorAIGVec *av0, *av1, *av2;
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *static_rho;
  BtorHashTableIterator it;
  char *indexed_name;
  const char *name;
  unsigned int count, i, len;
  int same_children_mem, j;
  int invert_av0 = 0;
  int invert_av1 = 0;
  int invert_av2 = 0;
  double start;
  bool restart;
  BtorIntHashTable *cache;

  assert (btor);
  assert (exp);

  start = btor_time_stamp ();
  mm    = btor->mm;
  avmgr = btor->avmgr;
  count = 0;
  cache = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (exp_stack);
  BTOR_PUSH_STACK (mm, exp_stack, exp);
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));

  while (!BTOR_EMPTY_STACK (exp_stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (exp_stack));

    if (BTOR_IS_SYNTH_NODE (cur)) continue;

    count++;
    if (!btor_contains_int_hash_table (cache, cur->id))
    {
      if (BTOR_IS_BV_CONST_NODE (cur))
      {
        cur->av = btor_const_aigvec (avmgr, btor_const_get_bits (cur));
        BTORLOG (2, "  synthesized: %s", node2string (cur));
        /* no need to call btor_aigvec_to_sat_tseitin here */
      }
      /* encode bv skeleton inputs: var, apply, feq */
      else if (BTOR_IS_BV_VAR_NODE (cur)
               || (BTOR_IS_APPLY_NODE (cur) && !cur->parameterized)
               || BTOR_IS_FEQ_NODE (cur))
      {
        assert (!cur->parameterized);
        cur->av = btor_var_aigvec (avmgr, btor_get_exp_width (btor, cur));

        if (BTOR_IS_BV_VAR_NODE (cur) && backannotation
            && (name = btor_get_symbol_exp (btor, cur)))
        {
          len = strlen (name) + 40;
          if (btor_get_exp_width (btor, cur) > 1)
          {
            indexed_name = btor_malloc (mm, len);
            for (i = 0; i < cur->av->len; i++)
            {
              b = btor_insert_in_ptr_hash_table (backannotation,
                                                 cur->av->aigs[i]);
              assert (b->key == cur->av->aigs[i]);
              sprintf (indexed_name, "%s[%d]", name, i);
              b->data.asStr = btor_strdup (mm, indexed_name);
            }
            btor_free (mm, indexed_name, len);
          }
          else
          {
            assert (btor_get_exp_width (btor, cur) == 1);
            b = btor_insert_in_ptr_hash_table (backannotation,
                                               cur->av->aigs[0]);
            assert (b->key == cur->av->aigs[0]);
            b->data.asStr = btor_strdup (mm, name);
          }
        }
        BTORLOG (2, "  synthesized: %s", node2string (cur));
        btor_aigvec_to_sat_tseitin (avmgr, cur->av);

        /* continue synthesizing children for apply and feq nodes if
         * lazy_synthesize is disabled */
        if (!btor->options.lazy_synthesize.val) goto PUSH_CHILDREN;
      }
      /* we stop at function nodes as they will be lazily synthesized and
       * encoded during consistency checking */
      else if (BTOR_IS_FUN_NODE (cur) && btor->options.lazy_synthesize.val)
      {
        continue;
      }
      else
      {
      PUSH_CHILDREN:
        assert (!btor->options.lazy_synthesize.val || !BTOR_IS_FUN_NODE (cur));

        btor_add_int_hash_table (cache, cur->id);
        BTOR_PUSH_STACK (mm, exp_stack, cur);
        for (j = cur->arity - 1; j >= 0; j--)
          BTOR_PUSH_STACK (mm, exp_stack, cur->e[j]);

        /* synthesize nodes in static_rho of lambda nodes */
        if (BTOR_IS_LAMBDA_NODE (cur))
        {
          static_rho = btor_lambda_get_static_rho (cur);
          if (static_rho)
          {
            btor_init_node_hash_table_iterator (&it, static_rho);
            while (btor_has_next_node_hash_table_iterator (&it))
            {
              value = it.bucket->data.asPtr;
              args  = btor_next_node_hash_table_iterator (&it);
              BTOR_PUSH_STACK (mm, exp_stack, btor_simplify_exp (btor, value));
              BTOR_PUSH_STACK (mm, exp_stack, btor_simplify_exp (btor, args));
            }
          }
        }
      }
    }
    /* paremterized nodes, argument nodes and functions are not
     * synthesizable */
    else if (!cur->parameterized && !BTOR_IS_ARGS_NODE (cur)
             && !BTOR_IS_FUN_NODE (cur))
    {
      if (!btor->options.lazy_synthesize.val)
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
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[i]);
            restart = true;
            break;
          }
        }
        if (restart) continue;
      }

      if (cur->arity == 1)
      {
        assert (cur->kind == BTOR_SLICE_NODE);
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
          case BTOR_BEQ_NODE: cur->av = btor_eq_aigvec (avmgr, av0, av1); break;
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
        if (!btor->options.lazy_synthesize.val)
          btor_aigvec_to_sat_tseitin (avmgr, cur->av);
      }
      else
      {
        assert (cur->arity == 3);

        if (BTOR_IS_BV_COND_NODE (cur))
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
  BTOR_RELEASE_STACK (mm, exp_stack);
  btor_free_int_hash_table (cache);

  if (count > 0 && btor->options.verbosity.val > 3)
    BTOR_MSG (
        btor->msg, 3, "synthesized %u expressions into AIG vectors", count);

  btor->time.synth_exp += btor_time_stamp () - start;
}

/* Mark all reachable expressions as reachable, reset reachable flag for all
 * previously reachable expressions that became unreachable due to rewriting. */
static void
update_reachable (Btor *btor, int check_all_tables)
{
  assert (btor);

  int i;
  double start;
  BtorNode *cur;
  BtorHashTableIterator it;

  assert (check_id_table_mark_unset_dbg (btor));
  assert (check_all_tables || btor->unsynthesized_constraints->count == 0);
  assert (check_all_tables || btor->embedded_constraints->count == 0);
  assert (check_all_tables || btor->varsubst_constraints->count == 0);

  start = btor_time_stamp ();
#ifndef NDEBUG
  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (cur)));
  }
#endif

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  if (check_all_tables)
  {
    btor_queue_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
    btor_queue_node_hash_table_iterator (&it, btor->embedded_constraints);
    btor_queue_node_hash_table_iterator (&it, btor->varsubst_constraints);
  }

  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    mark_exp (btor, cur, 1);
  }

  btor_init_node_hash_table_iterator (&it, btor->var_rhs);
  btor_queue_node_hash_table_iterator (&it, btor->fun_rhs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    mark_exp (btor, btor_simplify_exp (btor, cur), 1);
  }

  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;
    cur->reachable = cur->mark;
    cur->mark      = 0;
  }
  btor->time.reachable += btor_time_stamp () - start;
}

static void
mark_reachable (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int i;
  double start;
  BtorNode *cur;
  BtorNodePtrStack stack;

  start = btor_time_stamp ();
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (btor->mm, stack, exp);

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

    if (cur->reachable) continue;

    cur->reachable = 1;

    for (i = 0; i < cur->arity; i++)
      BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
  }

  BTOR_RELEASE_STACK (btor->mm, stack);
  btor->time.reachable += btor_time_stamp () - start;
}

/* forward assumptions to the SAT solver */
static void
add_again_assumptions (Btor *btor)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));

  int i;
  BtorNode *exp, *cur, *e;
  BtorNodePtrStack stack, unmark_stack;
  BtorPtrHashTable *assumptions;
  BtorHashTableIterator it;
  BtorAIG *aig;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;

  amgr = btor_get_aig_mgr_btor (btor);
  smgr = btor_get_sat_mgr_btor (btor);

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  assumptions = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    exp = btor_next_node_hash_table_iterator (&it);
    exp = btor_simplify_exp (btor, exp);

    if (BTOR_IS_INVERTED_NODE (exp) || !BTOR_IS_AND_NODE (exp))
    {
      if (!btor_find_in_ptr_hash_table (assumptions, exp))
        btor_insert_in_ptr_hash_table (assumptions, exp);
    }
    else
    {
      BTOR_PUSH_STACK (btor->mm, stack, exp);
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_POP_STACK (stack);
        assert (!BTOR_IS_INVERTED_NODE (cur));
        assert (BTOR_IS_AND_NODE (cur));
        assert (cur->mark == 0 || cur->mark == 1);
        if (cur->mark) continue;
        cur->mark = 1;
        BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);
        for (i = 0; i < 2; i++)
        {
          e = cur->e[i];
          if (!BTOR_IS_INVERTED_NODE (e) && BTOR_IS_AND_NODE (e))
            BTOR_PUSH_STACK (btor->mm, stack, e);
          else if (!btor_find_in_ptr_hash_table (assumptions, e))
            btor_insert_in_ptr_hash_table (assumptions, e);
        }
      }
    }
    mark_exp (btor, exp, 0);
  }

  btor_init_node_hash_table_iterator (&it, assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (btor_get_exp_width (btor, cur) == 1);
    assert (!BTOR_REAL_ADDR_NODE (cur)->simplified);
    aig = exp_to_aig (btor, cur);
    btor_aig_to_sat (amgr, aig);
    if (aig == BTOR_AIG_TRUE) continue;
    assert (BTOR_GET_CNF_ID_AIG (aig) != 0);
    btor_assume_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
    btor_release_aig (amgr, aig);
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (unmark_stack))->mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  btor_delete_ptr_hash_table (assumptions);
}

static int
timed_sat_sat (Btor *btor, int limit)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  double start, delta;
  int res;
  BtorSATMgr *smgr;

  smgr  = btor_get_sat_mgr_btor (btor);
  start = btor_time_stamp ();
  res   = btor_sat_sat (smgr, limit);
  delta = btor_time_stamp () - start;
  BTOR_CORE_SOLVER (btor)->time.sat += delta;

  BTOR_MSG (
      btor->msg, 2, "SAT solver returns %d after %.1f seconds", res, delta);

  return res;
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

static void
search_initial_applies_bv_skeleton (Btor *btor, BtorNodePtrStack *applies)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (applies);
  assert (BTOR_EMPTY_STACK (*applies));
  assert (check_id_table_aux_mark_unset_dbg (btor));

  double start;
  int i;
  BtorNode *cur;
  BtorNodePtrStack stack, unmark_stack;
  BtorHashTableIterator it;

  start = btor_time_stamp ();

  BTORLOG (1, "");
  BTORLOG (1, "*** search initial applies");

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark) continue;

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

      if (BTOR_IS_APPLY_NODE (cur) && !cur->parameterized)
      {
        //	      assert (BTOR_IS_SYNTH_NODE (cur));
        BTORLOG (1, "initial apply: %s", node2string (cur));
        BTOR_PUSH_STACK (btor->mm, *applies, cur);
        continue;
      }

      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);

  BTOR_CORE_SOLVER (btor)->time.search_init_apps += btor_time_stamp () - start;
}

static bool
has_bv_assignment (Btor *btor, BtorNode *exp)
{
  exp = BTOR_REAL_ADDR_NODE (exp);
  return (btor->bv_model
          && btor_find_in_ptr_hash_table (btor->bv_model, exp) != 0)
         || BTOR_IS_SYNTH_NODE (exp) || BTOR_IS_BV_CONST_NODE (exp);
}

static BtorBitVector *
get_bv_assignment (Btor *btor, BtorNode *exp)
{
  assert (btor->bv_model);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  BtorNode *real_exp;
  BtorBitVector *bv, *result;
  BtorPtrHashBucket *b;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  b        = btor_find_in_ptr_hash_table (btor->bv_model, real_exp);
  if (b)
    bv = btor_copy_bv (btor->mm, b->data.asPtr);
  else /* cache assignment to avoid querying the sat solver multiple times */
  {
    /* synthesized nodes are always encoded and have an assignment */
    if (BTOR_IS_SYNTH_NODE (real_exp))
      bv = btor_assignment_bv (btor->mm, real_exp, false);
    else if (BTOR_IS_BV_CONST_NODE (real_exp))
      bv = btor_copy_bv (btor->mm, btor_const_get_bits (real_exp));
    /* initialize var, apply, and feq nodes if they are not yet synthesized
     * and encoded (not in the BV skeleton yet, and thus unconstrained). */
    else if (BTOR_IS_BV_VAR_NODE (real_exp) || BTOR_IS_APPLY_NODE (real_exp)
             || BTOR_IS_FEQ_NODE (real_exp))
    {
      if (!BTOR_IS_SYNTH_NODE (real_exp))
        BTORLOG (1, "zero-initialize: %s", node2string (real_exp));
      bv = btor_assignment_bv (btor->mm, real_exp, true);
    }
    else
      bv = btor_eval_exp (btor, real_exp);
    btor_add_to_bv_model (btor, btor->bv_model, real_exp, bv);
  }

  if (BTOR_IS_INVERTED_NODE (exp))
  {
    result = btor_not_bv (btor->mm, bv);
    btor_free_bv (btor->mm, bv);
  }
  else
    result = bv;

  return result;
}

static void
assume_inputs (Btor *btor,
               Btor *clone,
               BtorNodePtrStack *inputs,
               BtorNodeMap *exp_map,
               BtorNodeMap *key_map,
               BtorNodeMap *assumptions)
{
  assert (btor);
  assert (clone);
  assert (inputs);
  assert (exp_map);
  assert (key_map);
  assert (key_map->table->count == 0);
  assert (assumptions);

  int i;
  BtorNode *cur_btor, *cur_clone, *bv_const, *bv_eq;
  BtorBitVector *bv;

  for (i = 0; i < BTOR_COUNT_STACK (*inputs); i++)
  {
    cur_btor  = BTOR_PEEK_STACK (*inputs, i);
    cur_clone = btor_mapped_node (exp_map, cur_btor);
    assert (cur_clone);
    assert (BTOR_IS_REGULAR_NODE (cur_clone));
    assert (!btor_mapped_node (key_map, cur_clone));
    btor_map_node (key_map, cur_clone, cur_btor);

    assert (BTOR_IS_REGULAR_NODE (cur_btor));
    bv       = get_bv_assignment (btor, cur_btor);
    bv_const = btor_const_exp (clone, bv);
    btor_free_bv (btor->mm, bv);
    bv_eq = btor_eq_exp (clone, cur_clone, bv_const);
    BTORLOG (1,
             "assume input: %s (%s)",
             node2string (cur_btor),
             node2string (bv_const));
    btor_assume_exp (clone, bv_eq);
    btor_map_node (assumptions, bv_eq, cur_clone);
    btor_release_exp (clone, bv_const);
    btor_release_exp (clone, bv_eq);
  }
}

static void
collect_applies (Btor *btor,
                 Btor *clone,
                 BtorNodeMap *key_map,
                 BtorNodeMap *assumptions,
                 BtorNodePtrStack *top_applies)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (clone);
  assert (key_map);
  assert (assumptions);

  double start;
  int i;
  BtorMemMgr *mm;
  BtorCoreSolver *slv;
  BtorNode *cur_btor, *cur_clone, *bv_eq;
  BtorNodePtrStack unmark_stack, failed_eqs;
  BtorNodeMapIterator it;

  start = btor_time_stamp ();

  mm  = btor->mm;
  slv = BTOR_CORE_SOLVER (btor);

  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (failed_eqs);

  btor_init_node_map_iterator (&it, assumptions);
  while (btor_has_next_node_map_iterator (&it))
  {
    bv_eq     = btor_next_node_map_iterator (&it);
    cur_clone = btor_mapped_node (assumptions, bv_eq);
    assert (cur_clone);
    /* Note: node mapping is normalized, revert */
    if (BTOR_IS_INVERTED_NODE (cur_clone))
    {
      bv_eq     = BTOR_INVERT_NODE (bv_eq);
      cur_clone = BTOR_INVERT_NODE (cur_clone);
    }
    cur_btor = btor_mapped_node (key_map, cur_clone);
    assert (cur_btor);
    assert (BTOR_IS_REGULAR_NODE (cur_btor));
    assert (BTOR_IS_BV_VAR_NODE (cur_btor) || BTOR_IS_APPLY_NODE (cur_btor)
            || BTOR_IS_FEQ_NODE (cur_btor));

    if (BTOR_IS_BV_VAR_NODE (cur_btor))
      slv->stats.dp_assumed_vars += 1;
    else if (BTOR_IS_FEQ_NODE (cur_btor))
      slv->stats.dp_assumed_eqs += 1;
    else
    {
      assert (BTOR_IS_APPLY_NODE (cur_btor));
      slv->stats.dp_assumed_applies += 1;
    }

    if (btor_failed_exp (clone, bv_eq))
    {
      BTORLOG (1, "failed: %s", node2string (cur_btor));
      if (BTOR_IS_BV_VAR_NODE (cur_btor))
        slv->stats.dp_failed_vars += 1;
      else if (BTOR_IS_FEQ_NODE (cur_btor))
      {
        slv->stats.dp_failed_eqs += 1;
        BTOR_PUSH_STACK (mm, failed_eqs, cur_btor);
      }
      else
      {
        assert (BTOR_IS_APPLY_NODE (cur_btor));
        if (cur_btor->aux_mark) continue;
        slv->stats.dp_failed_applies += 1;
        cur_btor->aux_mark = 1;
        BTOR_PUSH_STACK (mm, unmark_stack, cur_btor);
        BTOR_PUSH_STACK (mm, *top_applies, cur_btor);
      }
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (mm, unmark_stack);

  /* collect applies below failed function equalities */
  while (!BTOR_EMPTY_STACK (failed_eqs))
  {
    cur_btor = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (failed_eqs));

    if (!cur_btor->apply_below || cur_btor->aux_mark) continue;

    cur_btor->aux_mark = 1;
    BTOR_PUSH_STACK (mm, unmark_stack, cur_btor);

    /* we only need the "top applies" below a failed function equality */
    if (!cur_btor->parameterized && BTOR_IS_APPLY_NODE (cur_btor))
    {
      BTORLOG (1, "apply below eq: %s", node2string (cur_btor));
      BTOR_PUSH_STACK (mm, *top_applies, cur_btor);
      continue;
    }

    for (i = 0; i < cur_btor->arity; i++)
      BTOR_PUSH_STACK (mm, failed_eqs, cur_btor->e[i]);
  }
  BTOR_RELEASE_STACK (mm, failed_eqs);

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (mm, unmark_stack);

  slv->time.search_init_apps_collect_fa += btor_time_stamp () - start;
}

static void
set_up_dual_and_collect (Btor *btor,
                         Btor *clone,
                         BtorNode *clone_root,
                         BtorNodeMap *exp_map,
                         BtorNodePtrStack *inputs,
                         BtorNodePtrStack *top_applies,
                         int (*dp_cmp_inputs) (const void *, const void *))
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (clone);
  assert (clone_root);
  assert (exp_map);
  assert (inputs);
  assert (top_applies);
  assert (dp_cmp_inputs);

  double delta;
  BtorCoreSolver *slv;
  BtorNodeMap *assumptions, *key_map;

  delta = btor_time_stamp ();
  slv   = BTOR_CORE_SOLVER (btor);

  assumptions = btor_new_node_map (btor);
  key_map     = btor_new_node_map (btor);

  /* assume root */
  btor_assume_exp (clone, BTOR_INVERT_NODE (clone_root));

  /* assume assignments of bv vars and applies, partial assignments are
   * assumed as partial assignment (as slice on resp. var/apply) */
  qsort (inputs->start,
         BTOR_COUNT_STACK (*inputs),
         sizeof (BtorNode *),
         dp_cmp_inputs);
  assume_inputs (btor, clone, inputs, exp_map, key_map, assumptions);
  slv->time.search_init_apps_collect_var_apps += btor_time_stamp () - delta;

  /* let solver determine failed assumptions */
  delta = btor_time_stamp ();
  sat_aux_btor_dual_prop (clone);
  assert (clone->last_sat_result == BTOR_UNSAT);
  slv->time.search_init_apps_sat += btor_time_stamp () - delta;

  /* extract partial model via failed assumptions */
  collect_applies (btor, clone, key_map, assumptions, top_applies);

  btor_delete_node_map (assumptions);
  btor_delete_node_map (key_map);
}

static void
search_initial_applies_dual_prop (Btor *btor,
                                  Btor *clone,
                                  BtorNode *clone_root,
                                  BtorNodeMap *exp_map,
                                  BtorNodePtrStack *top_applies)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (clone);
  assert (clone_root);
  assert (exp_map);
  assert (top_applies);
  assert (check_id_table_aux_mark_unset_dbg (btor));

  double start;
  int i;
  BtorNode *cur;
  BtorNodePtrStack stack, unmark_stack, inputs;
  BtorHashTableIterator it;
  BtorSATMgr *smgr;
  BtorCoreSolver *slv;

  start = btor_time_stamp ();

  BTORLOG (1, "");
  BTORLOG (1, "*** search initial applies");

  slv                           = BTOR_CORE_SOLVER (btor);
  slv->stats.dp_failed_vars     = 0;
  slv->stats.dp_assumed_vars    = 0;
  slv->stats.dp_failed_applies  = 0;
  slv->stats.dp_assumed_applies = 0;

  smgr = btor_get_sat_mgr_btor (btor);
  if (!smgr->inc_required) return;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (inputs);

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark) continue;

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

      if (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_FEQ_NODE (cur)
          || BTOR_IS_APPLY_NODE (cur))
      {
        assert (BTOR_IS_SYNTH_NODE (cur));
        BTOR_PUSH_STACK (btor->mm, inputs, cur);
        continue;
      }

      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;

  (void) btor_cmp_exp_by_id_qsort_asc;

#if DP_QSORT == DP_QSORT_JUST
  btor_compute_scores_dual_prop (btor);
  set_up_dual_and_collect (btor,
                           clone,
                           clone_root,
                           exp_map,
                           &inputs,
                           top_applies,
                           btor_compare_scores_qsort);
#elif DP_QSORT == DP_QSORT_ASC
  set_up_dual_and_collect (btor,
                           clone,
                           clone_root,
                           exp_map,
                           &inputs,
                           top_applies,
                           btor_cmp_exp_by_id_qsort_asc);
#elif DP_QSORT == DP_QSORT_DESC
  set_up_dual_and_collect (btor,
                           clone,
                           clone_root,
                           exp_map,
                           &inputs,
                           top_applies,
                           btor_cmp_exp_by_id_qsort_desc);
#else

#if DP_QSORT_ASC_DESC_FIRST
  if (!slv->dp_cmp_inputs)
#endif
  {
    /* try different strategies and determine best */
    BtorNodePtrStack tmp_asc, tmp_desc;
    BTOR_INIT_STACK (tmp_asc);
    BTOR_INIT_STACK (tmp_desc);

    set_up_dual_and_collect (btor,
                             clone,
                             clone_root,
                             exp_map,
                             &inputs,
                             &tmp_desc,
                             btor_cmp_exp_by_id_qsort_desc);
    set_up_dual_and_collect (btor,
                             clone,
                             clone_root,
                             exp_map,
                             &inputs,
                             &tmp_asc,
                             btor_cmp_exp_by_id_qsort_asc);

    if (BTOR_COUNT_STACK (tmp_asc) < BTOR_COUNT_STACK (tmp_desc))
    {
      slv->dp_cmp_inputs = btor_cmp_exp_by_id_qsort_asc;
      for (i = 0; i < BTOR_COUNT_STACK (tmp_asc); i++)
        BTOR_PUSH_STACK (btor->mm, *top_applies, BTOR_PEEK_STACK (tmp_asc, i));
    }
    else
    {
      slv->dp_cmp_inputs = btor_cmp_exp_by_id_qsort_desc;
      for (i = 0; i < BTOR_COUNT_STACK (tmp_desc); i++)
        BTOR_PUSH_STACK (btor->mm, *top_applies, BTOR_PEEK_STACK (tmp_desc, i));
    }

    BTOR_RELEASE_STACK (btor->mm, tmp_asc);
    BTOR_RELEASE_STACK (btor->mm, tmp_desc);
  }
#if DP_QSORT_ASC_DESC_FIRST
  else
    set_up_dual_and_collect (btor,
                             clone,
                             clone_root,
                             exp_map,
                             &inputs,
                             top_applies,
                             slv->dp_cmp_inputs);
#endif
#endif

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  BTOR_RELEASE_STACK (btor->mm, inputs);

  slv->time.search_init_apps += btor_time_stamp () - start;
}

static void
search_initial_applies_just (Btor *btor, BtorNodePtrStack *top_applies)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (top_applies);
  assert (btor->unsynthesized_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);
  assert (check_id_table_aux_mark_unset_dbg (btor));

  int i, h;
  int a, a0, a1;
  double start;
  BtorNode *cur, *e0, *e1;
  BtorHashTableIterator it;
  BtorNodePtrStack stack, unmark_stack;
  BtorAIGMgr *amgr;

  start = btor_time_stamp ();

  BTORLOG (1, "");
  BTORLOG (1, "*** search initial applies");

  amgr = btor_get_aig_mgr_btor (btor);
  h    = btor->options.just_heuristic.val;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  btor_compute_scores (btor);

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark) continue;

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

      if (BTOR_IS_APPLY_NODE (cur) && !cur->parameterized)
      {
        BTORLOG (1, "initial apply: %s", node2string (cur));
        BTOR_PUSH_STACK (btor->mm, *top_applies, cur);
        continue;
      }

      if (!cur->parameterized && !BTOR_IS_FUN_NODE (cur)
          && btor_get_exp_width (btor, cur) == 1)
      {
        switch (cur->kind)
        {
          case BTOR_FEQ_NODE:
            a = BTOR_IS_SYNTH_NODE (cur)
                    ? btor_get_assignment_aig (amgr, cur->av->aigs[0])
                    : 0;  // 'x';

            if (a == 1 || a == 0) goto PUSH_CHILDREN;
            /* if equality is false (-1), we do not need to check
             * applies below for consistency as it is sufficient to
             * check the witnesses of inequality */
            break;

          case BTOR_AND_NODE:

            a = BTOR_IS_SYNTH_NODE (cur)
                    ? btor_get_assignment_aig (amgr, cur->av->aigs[0])
                    : 0;  // 'x'

            e0 = BTOR_REAL_ADDR_NODE (cur->e[0]);
            e1 = BTOR_REAL_ADDR_NODE (cur->e[1]);

            a0 = BTOR_IS_SYNTH_NODE (e0)
                     ? btor_get_assignment_aig (amgr, e0->av->aigs[0])
                     : 0;  // 'x'
            if (a0 && BTOR_IS_INVERTED_NODE (cur->e[0])) a0 *= -1;

            a1 = BTOR_IS_SYNTH_NODE (e1)
                     ? btor_get_assignment_aig (amgr, e1->av->aigs[0])
                     : 0;  // 'x'
            if (a1 && BTOR_IS_INVERTED_NODE (cur->e[1])) a1 *= -1;

            if (a != -1)  // and = 1 or x
            {
              BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
              BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
            }
            else  // and = 0
            {
              if (a0 == -1 && a1 == -1)  // both inputs 0
              {
                /* branch selection w.r.t selected heuristic */
                if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP
                    || h == BTOR_JUST_HEUR_BRANCH_MIN_DEP)
                {
                  if (btor_compare_scores (btor, cur->e[0], cur->e[1]))
                    BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
                  else
                    BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
                }
                else
                {
                  assert (h == BTOR_JUST_HEUR_LEFT);
                  BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
                }
              }
              else if (a0 == -1)  // only one input 0
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
              else if (a1 == -1)  // only one input 0
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
              else if (a0 == 0 && a1 == 1)  // first input x, second 0
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
              else if (a0 == 1 && a1 == 0)  // first input 0, second x
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
              else  // both inputs x
              {
                assert (a0 == 0);
                assert (a1 == 0);
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
              }
            }
            break;

#if 0
		  case BTOR_BCOND_NODE:
		    BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
		    c = bv_assignment_str_exp (btor, cur->e[0]);
		    if (c[0] == '1')  // then
		      BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
		    else if (c[0] == '0')
		      BTOR_PUSH_STACK (btor->mm, stack, cur->e[2]);
		    else                   // else
		      {
			BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
			BTOR_PUSH_STACK (btor->mm, stack, cur->e[2]);
		      }
		    btor_release_bv_assignment_str (btor, c);
		    break;
#endif

          default: goto PUSH_CHILDREN;
        }
      }
      else
      {
      PUSH_CHILDREN:
        for (i = 0; i < cur->arity; i++)
          BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
      }
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  BTOR_RELEASE_STACK (btor->mm, stack);

  BTOR_CORE_SOLVER (btor)->time.search_init_apps += btor_time_stamp () - start;
}

static bool
equal_bv_assignments (BtorNode *exp0, BtorNode *exp1)
{
  bool equal;
  Btor *btor;
  BtorBitVector *bv0, *bv1;

  btor  = BTOR_REAL_ADDR_NODE (exp0)->btor;
  bv0   = get_bv_assignment (btor, exp0);
  bv1   = get_bv_assignment (btor, exp1);
  equal = btor_compare_bv (bv0, bv1) == 0;
  btor_free_bv (btor->mm, bv0);
  btor_free_bv (btor->mm, bv1);
  return equal;
}

static int
compare_args_assignments (BtorNode *e0, BtorNode *e1)
{
  assert (BTOR_IS_REGULAR_NODE (e0));
  assert (BTOR_IS_REGULAR_NODE (e1));
  assert (BTOR_IS_ARGS_NODE (e0));
  assert (BTOR_IS_ARGS_NODE (e1));

  bool equal;
  BtorBitVector *bv0, *bv1;
  BtorNode *arg0, *arg1;
  Btor *btor;
  BtorArgsIterator it0, it1;
  btor = e0->btor;

  if (e0->sort_id != e1->sort_id) return 1;

  btor_init_args_iterator (&it0, e0);
  btor_init_args_iterator (&it1, e1);

  while (btor_has_next_args_iterator (&it0))
  {
    assert (btor_has_next_args_iterator (&it1));
    arg0 = btor_next_args_iterator (&it0);
    arg1 = btor_next_args_iterator (&it1);

    bv0 = get_bv_assignment (btor, arg0);
    bv1 = get_bv_assignment (btor, arg1);

    equal = btor_compare_bv (bv0, bv1) == 0;
    btor_free_bv (btor->mm, bv0);
    btor_free_bv (btor->mm, bv1);

    if (!equal) return 1;
  }

  return 0;
}

static unsigned int
hash_args_assignment (BtorNode *exp)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_ARGS_NODE (exp));

  unsigned int hash;
  Btor *btor;
  BtorNode *arg;
  BtorArgsIterator it;
  BtorBitVector *bv;

  btor = exp->btor;
  hash = 0;
  btor_init_args_iterator (&it, exp);
  while (btor_has_next_args_iterator (&it))
  {
    arg = btor_next_args_iterator (&it);
    bv  = get_bv_assignment (btor, arg);
    hash += btor_hash_bv (bv);
    btor_free_bv (btor->mm, bv);
  }
  return hash;
}

static void
collect_premisses (Btor *btor,
                   BtorNode *from,
                   BtorNode *to,
                   BtorNode *args,
                   BtorPtrHashTable *cond_sel_if,
                   BtorPtrHashTable *cond_sel_else)
{
  assert (btor);
  assert (from);
  assert (to);
  assert (cond_sel_if);
  assert (cond_sel_else);
  assert (BTOR_IS_REGULAR_NODE (from));
  assert (BTOR_IS_REGULAR_NODE (args));
  assert (BTOR_IS_ARGS_NODE (args));
  assert (BTOR_IS_REGULAR_NODE (to));

  BTORLOG (1,
           "%s: %s, %s, %s",
           __FUNCTION__,
           node2string (from),
           node2string (to),
           node2string (args));

  BtorMemMgr *mm;
  BtorNode *fun, *result;
  BtorPtrHashTable *t;
  BtorBitVector *bv_assignment;

  mm = btor->mm;

  /* follow propagation path and collect all conditions that have been
   * evaluated during propagation */
  if (BTOR_IS_APPLY_NODE (from))
  {
    assert (BTOR_IS_REGULAR_NODE (to));
    assert (BTOR_IS_FUN_NODE (to));

    fun = from->e[0];

    for (;;)
    {
      assert (BTOR_IS_REGULAR_NODE (fun));
      assert (BTOR_IS_FUN_NODE (fun));

      if (fun == to) break;

      if (BTOR_IS_FUN_COND_NODE (fun))
      {
        bv_assignment = get_bv_assignment (btor, fun->e[0]);

        /* propagate over function ite */
        if (btor_is_true_bv (bv_assignment))
        {
          result = fun->e[1];
          t      = cond_sel_if;
        }
        else
        {
          result = fun->e[2];
          t      = cond_sel_else;
        }
        btor_free_bv (mm, bv_assignment);
        if (!btor_find_in_ptr_hash_table (t, fun->e[0]))
          btor_insert_in_ptr_hash_table (t, btor_copy_exp (btor, fun->e[0]));
        fun = result;
        continue;
      }

      assert (BTOR_IS_LAMBDA_NODE (fun));

      btor_assign_args (btor, fun, args);
      result = btor_beta_reduce_partial_collect (
          btor, fun, cond_sel_if, cond_sel_else);
      btor_unassign_params (btor, fun);
      result = BTOR_REAL_ADDR_NODE (result);

      assert (BTOR_IS_APPLY_NODE (result));
      assert (result->e[1] == args);

      fun = result->e[0];
      btor_release_exp (btor, result);
    }
  }
  else
  {
    assert (BTOR_IS_LAMBDA_NODE (from));
    fun = from;

    btor_assign_args (btor, fun, args);
    result = btor_beta_reduce_partial_collect (
        btor, fun, cond_sel_if, cond_sel_else);
    btor_unassign_params (btor, fun);
    assert (BTOR_REAL_ADDR_NODE (result) == to);
    btor_release_exp (btor, result);
  }
}

static void
add_symbolic_lemma (Btor *btor,
                    BtorPtrHashTable *bconds_sel1,
                    BtorPtrHashTable *bconds_sel2,
                    BtorNode *a,
                    BtorNode *b,
                    BtorNode *args0,
                    BtorNode *args1)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (bconds_sel1);
  assert (bconds_sel2);
  assert (a);
  assert (b);
  assert (BTOR_IS_REGULAR_NODE (a));
  assert (BTOR_IS_APPLY_NODE (a));
  assert (BTOR_IS_REGULAR_NODE (args0));
  assert (BTOR_IS_ARGS_NODE (args0));
  assert (!args1 || BTOR_IS_REGULAR_NODE (b));
  assert (!args1 || BTOR_IS_APPLY_NODE (b));
  assert (!args1 || BTOR_IS_REGULAR_NODE (args1));
  assert (!args1 || BTOR_IS_ARGS_NODE (args1));
  assert (!a->parameterized);
  assert (!BTOR_REAL_ADDR_NODE (b)->parameterized);

  int lemma_size = 0;
  BtorCoreSolver *slv;
  BtorNode *cond, *eq, *and, *arg0, *arg1;
  BtorNode *premise = 0, *conclusion = 0, *lemma;
  BtorArgsIterator it0, it1;
  BtorHashTableIterator it;

  slv = BTOR_CORE_SOLVER (btor);

  BTORLOG (2, "lemma:");
  /* function congruence axiom conflict:
   *   apply arguments: a_0,...,a_n, b_0,...,b_n
   *   encode premisses: \forall i <= n . /\ a_i = b_i */
  if (args1)
  {
    assert (args0->sort_id == args1->sort_id);

    btor_init_args_iterator (&it0, args0);
    btor_init_args_iterator (&it1, args1);

    while (btor_has_next_args_iterator (&it0))
    {
      assert (btor_has_next_args_iterator (&it1));
      arg0 = btor_next_args_iterator (&it0);
      arg1 = btor_next_args_iterator (&it1);
      BTORLOG (2, "  p %s = %s", node2string (arg0), node2string (arg1));
      eq = btor_eq_exp (btor, arg0, arg1);
      if (premise)
      {
        and = btor_and_exp (btor, premise, eq);
        btor_release_exp (btor, premise);
        btor_release_exp (btor, eq);
        premise = and;
      }
      else
        premise = eq;

      lemma_size += 1;
    }
  }
  /* else beta reduction conflict */

  /* encode conclusion a = b */
  conclusion = btor_eq_exp (btor, a, b);

  lemma_size += 1; /* a == b */
  lemma_size += bconds_sel1->count;
  lemma_size += bconds_sel2->count;

  /* premisses bv conditions:
   *   true conditions: c_0, ..., c_k
   *   encode premisses: \forall i <= k. /\ c_i */
  btor_init_node_hash_table_iterator (&it, bconds_sel1);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cond = btor_next_node_hash_table_iterator (&it);
    BTORLOG (1, "  p %s", node2string (cond));
    assert (btor_get_exp_width (btor, cond) == 1);
    assert (!BTOR_REAL_ADDR_NODE (cond)->parameterized);
    if (premise)
    {
      and = btor_and_exp (btor, premise, cond);
      btor_release_exp (btor, premise);
      premise = and;
    }
    else
      premise = btor_copy_exp (btor, cond);
    btor_release_exp (btor, cond);
  }

  /* premisses bv conditions:
   *   false conditions: c_0, ..., c_l
   *   encode premisses: \forall i <= l. /\ \not c_i */
  btor_init_node_hash_table_iterator (&it, bconds_sel2);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cond = btor_next_node_hash_table_iterator (&it);
    BTORLOG (2, "  p %s", node2string (cond));
    assert (btor_get_exp_width (btor, cond) == 1);
    assert (!BTOR_REAL_ADDR_NODE (cond)->parameterized);
    if (premise)
    {
      and = btor_and_exp (btor, premise, BTOR_INVERT_NODE (cond));
      btor_release_exp (btor, premise);
      premise = and;
    }
    else
      premise = btor_copy_exp (btor, BTOR_INVERT_NODE (cond));
    btor_release_exp (btor, cond);
  }
  BTORLOG (2, "  c %s = %s", node2string (a), node2string (b));

  assert (conclusion);
  if (premise)
  {
    lemma = btor_implies_exp (btor, premise, conclusion);
    btor_release_exp (btor, premise);
  }
  else
    lemma = btor_copy_exp (btor, conclusion);

  /* delaying lemmas may in some cases produce the same lemmas with different *
   * conflicts */
  if (!btor_find_in_ptr_hash_table (slv->lemmas, lemma))
  {
    BTORLOG (2, "  lemma: %s", node2string (lemma));
    btor_insert_in_ptr_hash_table (slv->lemmas, btor_copy_exp (btor, lemma));
    BTOR_PUSH_STACK (btor->mm, slv->cur_lemmas, lemma);
    slv->stats.lod_refinements++;
    slv->stats.lemmas_size_sum += lemma_size;
    if (lemma_size >= BTOR_SIZE_STACK (slv->stats.lemmas_size))
      BTOR_FIT_STACK (btor->mm, slv->stats.lemmas_size, lemma_size);
    slv->stats.lemmas_size.start[lemma_size] += 1;
  }
  btor_release_exp (btor, lemma);
  btor_release_exp (btor, conclusion);
}

static void
add_lemma (Btor *btor, BtorNode *fun, BtorNode *app0, BtorNode *app1)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (fun);
  assert (app0);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_FUN_NODE (fun));
  assert (!fun->parameterized);
  assert (BTOR_IS_REGULAR_NODE (app0));
  assert (BTOR_IS_APPLY_NODE (app0));
  assert (!app1 || BTOR_IS_REGULAR_NODE (app1));
  assert (!app1 || BTOR_IS_APPLY_NODE (app1));

  double start;
  BtorPtrHashTable *cond_sel_if, *cond_sel_else;
  BtorNode *args, *value, *exp;
  BtorMemMgr *mm;

  mm    = btor->mm;
  start = btor_time_stamp ();

  /* collect intermediate conditions of bit vector conditionals */
  cond_sel_if   = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  cond_sel_else = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);

  /* function congruence axiom conflict */
  if (app1)
  {
    for (exp = app0; exp; exp = exp == app0 ? app1 : 0)
    {
      assert (exp);
      assert (BTOR_IS_APPLY_NODE (exp));
      args = exp->e[1];
      /* path from exp to conflicting fun */
      collect_premisses (btor, exp, fun, args, cond_sel_if, cond_sel_else);
    }
    add_symbolic_lemma (
        btor, cond_sel_if, cond_sel_else, app0, app1, app0->e[1], app1->e[1]);
  }
  /* beta reduction conflict */
  else
  {
    args = app0->e[1];
    btor_assign_args (btor, fun, args);
    value = btor_beta_reduce_partial (btor, fun, 0);
    btor_unassign_params (btor, fun);
    assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (value)));

    /* path from app0 to conflicting fun */
    collect_premisses (btor, app0, fun, args, cond_sel_if, cond_sel_else);

    /* path from conflicting fun to value */
    collect_premisses (btor,
                       fun,
                       BTOR_REAL_ADDR_NODE (value),
                       args,
                       cond_sel_if,
                       cond_sel_else);

    add_symbolic_lemma (
        btor, cond_sel_if, cond_sel_else, app0, value, app0->e[1], 0);
    btor_release_exp (btor, value);
  }

  btor_delete_ptr_hash_table (cond_sel_if);
  btor_delete_ptr_hash_table (cond_sel_else);
  BTOR_CORE_SOLVER (btor)->time.lemma_gen += btor_time_stamp () - start;
}

static void
push_applies_for_propagation (Btor *btor,
                              BtorNode *exp,
                              BtorNodePtrStack *prop_stack,
                              BtorIntHashTable *apply_search_cache)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (exp);
  assert (prop_stack);

  int i;
  double start;
  BtorCoreSolver *slv;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;

  start = btor_time_stamp ();
  slv   = BTOR_CORE_SOLVER (btor);
  mm    = btor->mm;

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, exp);
  do
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));
    assert (!cur->parameterized);
    assert (!BTOR_IS_FUN_NODE (cur));

    if (!cur->apply_below
        || btor_contains_int_hash_table (apply_search_cache, cur->id)
        || BTOR_IS_FEQ_NODE (cur))
      continue;

    btor_add_int_hash_table (apply_search_cache, cur->id);

    if (BTOR_IS_APPLY_NODE (cur))
    {
      BTOR_PUSH_STACK (mm, *prop_stack, cur);
      BTOR_PUSH_STACK (mm, *prop_stack, cur->e[0]);
      continue;
    }

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  } while (!BTOR_EMPTY_STACK (visit));
  BTOR_RELEASE_STACK (mm, visit);
  slv->time.find_prop_app += btor_time_stamp () - start;
}

static void
propagate (Btor *btor,
           BtorNodePtrStack *prop_stack,
           BtorPtrHashTable *cleanup_table,
           BtorIntHashTable *apply_search_cache)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (prop_stack);
  assert (cleanup_table);
  assert (apply_search_cache);

  bool prop_down, conflict;
  BtorBitVector *bv;
  BtorMemMgr *mm;
  BtorCoreSolver *slv;
  BtorNode *fun, *app, *args, *fun_value, *cur;
  BtorNode *hashed_app;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorPtrHashTable *conds;

  mm  = btor->mm;
  slv = BTOR_CORE_SOLVER (btor);

  BTORLOG (1, "");
  BTORLOG (1, "*** %s", __FUNCTION__);
  while (!BTOR_EMPTY_STACK (*prop_stack))
  {
    fun = BTOR_POP_STACK (*prop_stack);
    assert (BTOR_IS_REGULAR_NODE (fun));
    assert (BTOR_IS_FUN_NODE (fun));
    assert (!fun->simplified);
    assert (!BTOR_EMPTY_STACK (*prop_stack));
    app = BTOR_POP_STACK (*prop_stack);
    assert (BTOR_IS_REGULAR_NODE (app));
    assert (BTOR_IS_APPLY_NODE (app));
    assert (app->refs - app->ext_refs > 0);

    conflict = false;

    if (app->propagated) continue;

    app->propagated = 1;
    if (!btor_find_in_ptr_hash_table (cleanup_table, app))
      btor_insert_in_ptr_hash_table (cleanup_table, app);
    slv->stats.propagations++;

    BTORLOG (1, "propagate");
    BTORLOG (1, "  app: %s", node2string (app));
    BTORLOG (1, "  fun: %s", node2string (fun));

    args = app->e[1];
    assert (BTOR_IS_REGULAR_NODE (args));
    assert (BTOR_IS_ARGS_NODE (args));

    push_applies_for_propagation (btor, args, prop_stack, apply_search_cache);

    if (!fun->rho)
    {
      fun->rho =
          btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) hash_args_assignment,
                                   (BtorCmpPtr) compare_args_assignments);
      if (!btor_find_in_ptr_hash_table (cleanup_table, fun))
        btor_insert_in_ptr_hash_table (cleanup_table, fun);
    }
    else
    {
      b = btor_find_in_ptr_hash_table (fun->rho, args);
      if (b)
      {
        hashed_app = (BtorNode *) b->data.asPtr;
        assert (BTOR_IS_REGULAR_NODE (hashed_app));
        assert (BTOR_IS_APPLY_NODE (hashed_app));

        /* function congruence conflict */
        if (!equal_bv_assignments (hashed_app, app))
        {
          BTORLOG (1, "\e[1;31m");
          BTORLOG (1, "FC conflict at: %s", node2string (fun));
          BTORLOG (1, "add_lemma:");
          BTORLOG (1, "  fun: %s", node2string (fun));
          BTORLOG (1, "  app1: %s", node2string (hashed_app));
          BTORLOG (1, "  app2: %s", node2string (app));
          BTORLOG (1, "\e[0;39m");
          slv->stats.function_congruence_conflicts++;
          add_lemma (btor, fun, hashed_app, app);
          conflict = true;
          /* stop at first conflict */
          if (!btor->options.eager_lemmas.val) break;
        }
        continue;
      }
    }
    assert (fun->rho);
    assert (!btor_find_in_ptr_hash_table (fun->rho, args));
    btor_insert_in_ptr_hash_table (fun->rho, args)->data.asPtr = app;
    BTORLOG (1, "  save app: %s (%s)", node2string (args), node2string (app));

    /* skip array vars/uf */
    if (BTOR_IS_UF_NODE (fun)) continue;

    if (BTOR_IS_FUN_COND_NODE (fun))
    {
      push_applies_for_propagation (
          btor, fun->e[0], prop_stack, apply_search_cache);
      bv = get_bv_assignment (btor, fun->e[0]);

      /* propagate over function ite */
      BTORLOG (1, "  propagate down: %s", node2string (app));
      app->propagated = 0;
      BTOR_PUSH_STACK (mm, *prop_stack, app);
      if (btor_is_true_bv (bv))
        BTOR_PUSH_STACK (mm, *prop_stack, fun->e[1]);
      else
        BTOR_PUSH_STACK (mm, *prop_stack, fun->e[2]);
      btor_free_bv (mm, bv);
      continue;
    }

    assert (BTOR_IS_LAMBDA_NODE (fun));
    conds = btor_new_ptr_hash_table (mm,
                                     (BtorHashPtr) btor_hash_exp_by_id,
                                     (BtorCmpPtr) btor_compare_exp_by_id);
    btor_assign_args (btor, fun, args);
    fun_value = btor_beta_reduce_partial (btor, fun, conds);
    assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (fun_value)));
    btor_unassign_params (btor, fun);

    prop_down = false;
    // TODO: how can we still propagate negated applies down?
    if (!BTOR_IS_INVERTED_NODE (fun_value) && BTOR_IS_APPLY_NODE (fun_value))
      prop_down = fun_value->e[1] == args;

    /* NOTE: this is a special case 'fun_value' is a function application and
     * is not encoded.  the value of 'fun_value' must be the same as 'app'.
     * if 'fun_value' and 'app' have the same number of arguments and the
     * arguments have the same value, we can propagate 'app' instead of
     * 'fun_value'. in this case, we do not have to additionally encode
     * 'fun_value', but we can use 'app' instead, which has the same
     * properties as 'fun_value'. further, we do not have to encode every
     * intermediate function application we encounter while propagating
     * 'app'. */
    if (prop_down)
    {
      assert (BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (fun_value)));
      BTOR_PUSH_STACK (mm, *prop_stack, app);
      BTOR_PUSH_STACK (mm, *prop_stack, BTOR_REAL_ADDR_NODE (fun_value)->e[0]);
      slv->stats.propagations_down++;
      app->propagated = 0;
      BTORLOG (1, "  propagate down: %s", node2string (app));
    }
    else if (!equal_bv_assignments (app, fun_value))
    {
      BTORLOG (1, "\e[1;31m");
      BTORLOG (1, "BR conflict at: %s", node2string (fun));
      BTORLOG (1, "add_lemma:");
      BTORLOG (1, "  fun: %s", node2string (fun));
      BTORLOG (1, "  app: %s", node2string (app));
      BTORLOG (1, "\e[0;39m");
      slv->stats.beta_reduction_conflicts++;
      add_lemma (btor, fun, app, 0);
      conflict = true;
    }

    /* we have a conflict and the values are inconsistent, we do not have
     * to push applies onto 'prop_stack' that produce this inconsistent
     * value */
    if (conflict)
    {
      btor_init_node_hash_table_iterator (&it, conds);
      while (btor_has_next_node_hash_table_iterator (&it))
        btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
    }
    /* push applies onto 'prop_stack' that are necesary to derive 'fun_value'
     */
    else
    {
      /* in case of down propagation 'fun_value' is a function application
       * and we can propagate 'app' instead. hence, we to not have to
       * push 'fun_value' onto 'prop_stack'. */
      if (!prop_down)
        push_applies_for_propagation (
            btor, fun_value, prop_stack, apply_search_cache);

      /* push applies in evaluated conditions */
      btor_init_node_hash_table_iterator (&it, conds);
      while (btor_has_next_node_hash_table_iterator (&it))
      {
        cur = btor_next_node_hash_table_iterator (&it);
        push_applies_for_propagation (
            btor, cur, prop_stack, apply_search_cache);
        btor_release_exp (btor, cur);
      }
    }
    btor_delete_ptr_hash_table (conds);
    btor_release_exp (btor, fun_value);

    /* stop at first conflict */
    if (!btor->options.eager_lemmas.val && conflict) break;
  }
}

/* generate hash table for function 'fun' consisting of all rho and static_rho
 * hash tables. */
static BtorPtrHashTable *
generate_table (Btor *btor, BtorNode *fun)
{
  int i;
  BtorMemMgr *mm;
  BtorNode *cur, *value, *args;
  BtorPtrHashTable *table, *rho, *static_rho;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorHashTableIterator it;
  BtorBitVector *evalbv;

  mm    = btor->mm;
  table = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) hash_args_assignment,
                                   (BtorCmpPtr) compare_args_assignments);
  cache = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, fun);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cache, cur->id)
        || (!BTOR_IS_FUN_NODE (cur) && !cur->parameterized))
      continue;

    btor_add_int_hash_table (cache, cur->id);

    if (BTOR_IS_FUN_NODE (cur))
    {
      assert (cur->is_array);
      rho        = cur->rho;
      static_rho = 0;

      if (BTOR_IS_LAMBDA_NODE (cur))
      {
        static_rho = btor_lambda_get_static_rho (cur);
        assert (static_rho);
      }
      else if (BTOR_IS_FUN_COND_NODE (cur))
      {
        evalbv = get_bv_assignment (btor, cur->e[0]);
        if (btor_is_true_bv (evalbv))
          BTOR_PUSH_STACK (mm, visit, cur->e[1]);
        else
          BTOR_PUSH_STACK (mm, visit, cur->e[2]);
        btor_free_bv (mm, evalbv);
      }

      if (rho)
      {
        btor_init_node_hash_table_iterator (&it, rho);
        if (static_rho) btor_queue_node_hash_table_iterator (&it, static_rho);
      }
      else if (static_rho)
        btor_init_node_hash_table_iterator (&it, static_rho);

      if (rho || static_rho)
      {
        while (btor_has_next_node_hash_table_iterator (&it))
        {
          value = it.bucket->data.asPtr;
          assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (value)));
          args = btor_next_node_hash_table_iterator (&it);
          assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (args)));

          if (!btor_find_in_ptr_hash_table (table, args))
            btor_insert_in_ptr_hash_table (table, args)->data.asPtr = value;
        }
      }

      if (BTOR_IS_FUN_COND_NODE (cur)) continue;
    }

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  BTOR_RELEASE_STACK (mm, visit);
  btor_free_int_hash_table (cache);

  return table;
}

static void
add_extensionality_lemmas (Btor *btor)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  bool skip;
  BtorBitVector *evalbv;
  unsigned num_lemmas = 0;
  BtorNode *cur, *cur_args, *app0, *app1, *eq, *con, *value;
  BtorHashTableIterator it;
  BtorPtrHashTable *table0, *table1, *conflicts;
  BtorHashTableIterator hit;
  BtorNodePtrStack feqs;
  BtorMemMgr *mm;
  BtorPtrHashBucket *b;
  BtorCoreSolver *slv;

  BTORLOG (1, "");
  BTORLOG (1, "*** %s", __FUNCTION__);

  slv = BTOR_CORE_SOLVER (btor);
  mm  = btor->mm;
  BTOR_INIT_STACK (feqs);

  /* collect all reachable function equalities */
  btor_init_node_hash_table_iterator (&it, btor->feqs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_FEQ_NODE (cur));
    if (!cur->reachable) continue;
    BTOR_PUSH_STACK (btor->mm, feqs, cur);
  }

  while (!BTOR_EMPTY_STACK (feqs))
  {
    cur = BTOR_POP_STACK (feqs);
    assert (BTOR_IS_FEQ_NODE (cur));
    assert (cur->reachable);
    assert (cur->e[0]->is_array);
    assert (cur->e[1]->is_array);

    evalbv = get_bv_assignment (btor, cur);
    assert (evalbv);
    skip = btor_is_false_bv (evalbv);
    btor_free_bv (btor->mm, evalbv);

    if (skip) continue;

    table0 = generate_table (btor, cur->e[0]);
    table1 = generate_table (btor, cur->e[1]);

    conflicts = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) hash_args_assignment,
                                         (BtorCmpPtr) compare_args_assignments);

    btor_init_node_hash_table_iterator (&hit, table0);
    while (btor_has_next_node_hash_table_iterator (&hit))
    {
      value    = hit.bucket->data.asPtr;
      cur_args = btor_next_node_hash_table_iterator (&hit);
      b        = btor_find_in_ptr_hash_table (table1, cur_args);

      if (btor_find_in_ptr_hash_table (conflicts, cur_args)) continue;

      if (!b || !equal_bv_assignments (value, b->data.asPtr))
        btor_insert_in_ptr_hash_table (conflicts, cur_args);
    }

    btor_init_node_hash_table_iterator (&hit, table1);
    while (btor_has_next_node_hash_table_iterator (&hit))
    {
      value    = hit.bucket->data.asPtr;
      cur_args = btor_next_node_hash_table_iterator (&hit);
      b        = btor_find_in_ptr_hash_table (table0, cur_args);

      if (btor_find_in_ptr_hash_table (conflicts, cur_args)) continue;

      if (!b || !equal_bv_assignments (value, b->data.asPtr))
        btor_insert_in_ptr_hash_table (conflicts, cur_args);
    }

    BTORLOG (1, "  %s", node2string (cur));
    btor_init_node_hash_table_iterator (&hit, conflicts);
    while (btor_has_next_node_hash_table_iterator (&hit))
    {
      cur_args = btor_next_node_hash_table_iterator (&hit);
      app0     = btor_apply_exp (btor, cur->e[0], cur_args);
      app1     = btor_apply_exp (btor, cur->e[1], cur_args);
      eq       = btor_eq_exp (btor, app0, app1);
      con      = btor_implies_exp (btor, cur, eq);

      /* add instantiation of extensionality lemma */
      if (!btor_find_in_ptr_hash_table (slv->lemmas, con))
      {
        btor_insert_in_ptr_hash_table (slv->lemmas, btor_copy_exp (btor, con));
        BTOR_PUSH_STACK (btor->mm, slv->cur_lemmas, con);
        slv->stats.extensionality_lemmas++;
        slv->stats.lod_refinements++;
        num_lemmas++;
        BTORLOG (1, "    %s, %s", node2string (app0), node2string (app1));
      }
      btor_release_exp (btor, app0);
      btor_release_exp (btor, app1);
      btor_release_exp (btor, eq);
      btor_release_exp (btor, con);
    }
    btor_delete_ptr_hash_table (conflicts);
    btor_delete_ptr_hash_table (table0);
    btor_delete_ptr_hash_table (table1);
  }
  BTOR_RELEASE_STACK (btor->mm, feqs);

  BTORLOG (1, "  added %u extensionality lemmas", num_lemmas);
}

static void
check_and_resolve_conflicts (Btor *btor,
                             Btor *clone,
                             BtorNode *clone_root,
                             BtorNodeMap *exp_map)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  bool found_conflicts;
  BtorMemMgr *mm;
  BtorCoreSolver *slv;
  BtorNode *app, *cur;
  BtorNodePtrStack prop_stack;
  BtorNodePtrStack top_applies;
  BtorPtrHashTable *cleanup_table;
  BtorIntHashTable *apply_search_cache;
  BtorHashTableIterator it;

  slv                = BTOR_CORE_SOLVER (btor);
  apply_search_cache = 0;
  found_conflicts    = false;
  mm                 = btor->mm;
  slv                = BTOR_CORE_SOLVER (btor);

  /* initialize new bit vector model, which will be constructed while
   * consistency checking. this also deletes the model from the previous run */
  btor_init_bv_model (btor, &btor->bv_model);

  assert (!found_conflicts);
  cleanup_table = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (prop_stack);
  BTOR_INIT_STACK (top_applies);

  /* cache applies that were visited while searching for applies to propagate.
   * applies added to this cache will be skipped in the apply search the next
   * time they are visited.
   * Note: the id of the resp. apply will be added to 'apply_search_cache',
   *       hence, we don't have to ensure that these applies still exist in
   *       memory.
   */
  if (!apply_search_cache) apply_search_cache = btor_new_int_hash_table (mm);

  if (clone)
    search_initial_applies_dual_prop (
        btor, clone, clone_root, exp_map, &top_applies);
  else if (btor->options.just.val)
    search_initial_applies_just (btor, &top_applies);
  else
    search_initial_applies_bv_skeleton (btor, &top_applies);

  /* var_rhs are always part of the formula (due to the implicit top level
   * equality). thus, we need to check the underlying applies for consistency.
   * this also applies for don't care reasoning.
   */
  btor_init_node_hash_table_iterator (&it, btor->var_rhs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_simplify_exp (btor, btor_next_node_hash_table_iterator (&it));
    push_applies_for_propagation (btor, cur, &prop_stack, apply_search_cache);
  }

  while (!BTOR_EMPTY_STACK (top_applies))
  {
    app = BTOR_POP_STACK (top_applies);
    assert (BTOR_IS_REGULAR_NODE (app));
    assert (BTOR_IS_APPLY_NODE (app));
    assert (app->reachable);
    assert (!app->parameterized);
    assert (!app->propagated);
    BTOR_PUSH_STACK (mm, prop_stack, app);
    BTOR_PUSH_STACK (mm, prop_stack, app->e[0]);
  }

  propagate (btor, &prop_stack, cleanup_table, apply_search_cache);
  found_conflicts = BTOR_COUNT_STACK (slv->cur_lemmas) > 0;

  if (!found_conflicts && btor->feqs->count > 0)
  {
    assert (BTOR_EMPTY_STACK (prop_stack));
    add_extensionality_lemmas (btor);
    found_conflicts = BTOR_COUNT_STACK (slv->cur_lemmas) > 0;
  }

  /* applies may have assignments that were not checked for consistency, which
   * is the case when they are not required for deriving SAT (don't care
   * reasoning). hence, we remove those applies from the 'bv_model' as they do
   * not have a valid assignment. an assignment will be generated during
   * model construction */
  if (!found_conflicts)
  {
    btor_init_node_hash_table_iterator (&it, btor->bv_model);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      if (BTOR_IS_APPLY_NODE (cur) && !cur->propagated)
        btor_remove_from_bv_model (btor, btor->bv_model, cur);
    }
  }

  btor_init_node_hash_table_iterator (&it, cleanup_table);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (BTOR_IS_APPLY_NODE (cur))
    {
      /* generate model for apply */
      if (!found_conflicts)
        btor_free_bv (btor->mm, get_bv_assignment (btor, cur));
      cur->propagated = 0;
    }
    else
    {
      assert (BTOR_IS_FUN_NODE (cur));
      assert (cur->rho);

      if (found_conflicts)
      {
        btor_delete_ptr_hash_table (cur->rho);
        cur->rho = 0;
      }
      else
      {
        /* remember functions for incremental usage (and prevent
         * premature release in case that function is released via API
         * call) */
        BTOR_PUSH_STACK (
            mm, btor->functions_with_model, btor_copy_exp (btor, cur));
      }
    }
  }
  btor_delete_ptr_hash_table (cleanup_table);
  BTOR_RELEASE_STACK (mm, prop_stack);
  BTOR_RELEASE_STACK (mm, top_applies);

  btor_free_int_hash_table (apply_search_cache);
  apply_search_cache = 0;
}

static Btor *
new_exp_layer_clone_for_dual_prop (Btor *btor,
                                   BtorNodeMap **exp_map,
                                   BtorNode **root)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (exp_map);
  assert (root);

  double start;
  Btor *clone;
  BtorNode *cur, *and;
  BtorHashTableIterator it;
  BtorSATMgr *smgr;

  start = btor_time_stamp ();

  clone = btor_clone_exp_layer (btor, exp_map);
  assert (!clone->synthesized_constraints->count);
  assert (clone->unsynthesized_constraints->count);

  clone->options.model_gen.val   = 0;
  clone->options.incremental.val = 1;
#ifdef BTOR_CHECK_MODEL
  /* cleanup dangling references when model validation is enabled */
  clone->options.auto_cleanup_internal.val = 1;
#endif
#ifndef NBTORLOG
  clone->options.loglevel.val = 0;
#endif
  clone->options.verbosity.val = 0;
  clone->options.dual_prop.val = 0;

  smgr = btor_get_sat_mgr_btor (clone);
  assert (!btor_is_initialized_sat (smgr));
  btor_set_sat_solver (smgr, btor_get_sat_mgr_btor (btor)->name, "plain=1", 0);
  btor_init_sat (smgr);

  btor_init_node_hash_table_iterator (&it, clone->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, clone->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_REAL_ADDR_NODE (cur)->constraint = 0;
    if (!*root)
    {
      *root = btor_copy_exp (clone, cur);
    }
    else
    {
      and = btor_and_exp (clone, *root, cur);
      btor_release_exp (clone, *root);
      *root = and;
    }
  }

  btor_init_node_hash_table_iterator (&it, clone->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, clone->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (clone, btor_next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (clone->unsynthesized_constraints);
  btor_delete_ptr_hash_table (clone->assumptions);
  clone->unsynthesized_constraints =
      btor_new_ptr_hash_table (clone->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  clone->assumptions =
      btor_new_ptr_hash_table (clone->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_CORE_SOLVER (btor)->time.search_init_apps_cloning +=
      btor_time_stamp () - start;
  return clone;
}

static void
add_lemma_to_dual_prop_clone (Btor *btor,
                              Btor *clone,
                              BtorNode **root,
                              BtorNode *lemma,
                              BtorNodeMap *exp_map)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (clone);
  assert (lemma);

  BtorNode *clemma, *and;

  /* clone and rebuild lemma with rewrite level 0 (as we want the exact
   * expression) */
  clemma = btor_recursively_rebuild_exp_clone (btor, clone, lemma, exp_map, 0);
  assert (clemma);
  and = btor_and_exp (clone, *root, clemma);
  btor_release_exp (clone, clemma);
  btor_release_exp (clone, *root);
  *root = and;
}

static BtorNode *
create_function_inequality (Btor *btor, BtorNode *feq)
{
  assert (BTOR_IS_REGULAR_NODE (feq));
  assert (BTOR_IS_FEQ_NODE (feq));

  BtorMemMgr *mm;
  BtorNode *var, *app0, *app1, *eq, *arg;
  BtorSortUniqueTable *sorts;
  BtorSortId funsort, sort;
  BtorNodePtrStack args;
  BtorTupleSortIterator it;

  BTOR_INIT_STACK (args);

  mm      = btor->mm;
  sorts   = &btor->sorts_unique_table;
  funsort = btor_get_domain_fun_sort (sorts, feq->e[0]->sort_id);

  btor_init_tuple_sort_iterator (&it, sorts, funsort);
  while (btor_has_next_tuple_sort_iterator (&it))
  {
    sort = btor_next_tuple_sort_iterator (&it);
    assert (btor_is_bitvec_sort (sorts, sort));
    var = btor_var_exp (btor, btor_get_width_bitvec_sort (sorts, sort), 0);
    BTOR_PUSH_STACK (mm, args, var);
  }

  arg  = btor_args_exp (btor, BTOR_COUNT_STACK (args), args.start);
  app0 = btor_apply_exp_node (btor, feq->e[0], arg);
  app1 = btor_apply_exp_node (btor, feq->e[1], arg);
  eq   = btor_eq_exp (btor, app0, app1);

  btor_release_exp (btor, arg);
  btor_release_exp (btor, app0);
  btor_release_exp (btor, app1);
  while (!BTOR_EMPTY_STACK (args))
    btor_release_exp (btor, BTOR_POP_STACK (args));
  BTOR_RELEASE_STACK (mm, args);

  return BTOR_INVERT_NODE (eq);
}

/* for every function equality f = g, add
 * f != g -> f(a) != g(a) */
static void
add_function_inequality_constraints (Btor *btor)
{
  BtorNode *cur, *neq, *con;
  BtorNodePtrStack feqs;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;

  /* we have to add inequality constraints for every function equality
   * in the formula (var_rhs and fun_rhs are still part of the formula). */
  btor_init_node_hash_table_iterator (&it, btor->var_rhs);
  btor_queue_node_hash_table_iterator (&it, btor->fun_rhs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    cur = btor_simplify_exp (btor, cur);
    mark_reachable (btor, cur);
  }

  /* collect all reachable function equalities */
  BTOR_INIT_STACK (feqs);
  btor_init_node_hash_table_iterator (&it, btor->feqs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    b   = it.bucket;
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_FEQ_NODE (cur));
    if (!cur->reachable || b->data.asInt) continue;
    mark_reachable (btor, cur);
    BTOR_PUSH_STACK (btor->mm, feqs, cur);
    b->data.asInt = 1; /* mark function equality for inequality witness */
    BTOR_ABORT_CORE (
        (!cur->e[0]->is_array || !cur->e[1]->is_array)
            && (!BTOR_IS_UF_NODE (cur->e[0]) || !BTOR_IS_UF_NODE (cur->e[1])),
        "equality over lambda not supported yet");
  }

  /* add inequality constraint for every reachable function equality */
  while (!BTOR_EMPTY_STACK (feqs))
  {
    cur = BTOR_POP_STACK (feqs);
    assert (BTOR_IS_FEQ_NODE (cur));
    assert (!cur->parameterized);
    assert (cur->reachable);
    neq = create_function_inequality (btor, cur);
    con = btor_implies_exp (btor, BTOR_INVERT_NODE (cur), neq);
    btor_assert_exp (btor, con);
    btor_release_exp (btor, con);
    btor_release_exp (btor, neq);
    BTORLOG (2, "add inequality constraint for %s", node2string (cur));
  }
  BTOR_RELEASE_STACK (btor->mm, feqs);
}

static int
sat_aux_btor_dual_prop (Btor *btor)
{
  assert (btor);

  int sat_result;
  BtorSATMgr *smgr;
#ifdef BTOR_CHECK_FAILED
  Btor *faclone = 0;
#endif

  if (btor->inconsistent) goto DONE;

  BTOR_MSG (btor->msg, 1, "calling SAT");

#ifdef BTOR_CHECK_FAILED
  if (btor_has_clone_support_sat_mgr (btor_get_sat_mgr_btor (btor))
      && btor->options.chk_failed_assumptions.val)
  {
    faclone                                     = btor_clone_btor (btor);
    faclone->options.auto_cleanup.val           = 1;
    faclone->options.auto_cleanup_internal.val  = 1;
    faclone->options.loglevel.val               = 0;
    faclone->options.verbosity.val              = 0;
    faclone->options.chk_failed_assumptions.val = 0;
    faclone->options.dual_prop.val              = 0;  // FIXME necessary?
  }
#endif

  smgr = btor_get_sat_mgr_btor (btor);

  if (!btor_is_initialized_sat (smgr)) btor_init_sat (smgr);

  if (btor->valid_assignments == 1) reset_incremental_usage (btor);

  if (btor->feqs->count > 0)
  {
    // TODO (ma): check if function equalities are arrays only
    update_reachable (btor, 1);
    add_function_inequality_constraints (btor);
  }

  assert (btor->synthesized_constraints->count == 0);
  assert (btor->unsynthesized_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);
  assert (check_all_hash_tables_proxy_free_dbg (btor));
  assert (check_all_hash_tables_simp_free_dbg (btor));

#ifndef NDEBUG
  BtorHashTableIterator it;
  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    assert (!BTOR_REAL_ADDR_NODE (btor_next_node_hash_table_iterator (&it))
                 ->simplified);
#endif

  update_reachable (btor, 0);
  assert (check_reachable_flag_dbg (btor));

  add_again_assumptions (btor);
  assert (check_reachable_flag_dbg (btor));

  sat_result = timed_sat_sat (btor, -1);

  assert (sat_result == BTOR_UNSAT
          || (btor_terminate_btor (btor) && sat_result == BTOR_UNKNOWN));

DONE:
  sat_result              = BTOR_UNSAT;
  btor->valid_assignments = 1;

  btor->last_sat_result = sat_result;
#ifdef BTOR_CHECK_FAILED
  if (faclone && btor->options.chk_failed_assumptions.val)
  {
    if (!btor->inconsistent && btor->last_sat_result == BTOR_UNSAT)
      check_failed_assumptions (btor, faclone);
    btor_delete_btor (faclone);
  }
#endif
  return sat_result;
}

#ifdef BTOR_ENABLE_BETA_REDUCTION_PROBING
static uint32_t
sum_ops (Btor *btor)
{
  int i;
  uint32_t sum = 0;

  for (i = BTOR_BV_CONST_NODE; i < BTOR_PROXY_NODE; i++)
    sum += btor->ops[i].cur;
  return sum;
}

static int
br_probe (Btor *btor)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (btor->avmgr);
  assert (btor->avmgr->amgr);
  assert (btor->avmgr->amgr->smgr);
  assert (btor_has_clone_support_sat_mgr (btor_get_sat_mgr_btor (btor)));

  Btor *clone;
  int res;
  uint32_t num_ops_orig, num_ops_clone;
  double start, delta;

  if (btor->last_sat_result || btor->options.incremental.val
      || btor->options.model_gen.val || btor->options.beta_reduce_all.val
      || (btor->lambdas->count == 0 && btor->ufs->count == 0))
    return BTOR_UNKNOWN;

  start = btor_time_stamp ();

  BTOR_MSG (btor->msg, 1, "try full beta reduction probing");
  assert (btor->assumptions->count == 0);
  clone                              = btor_clone_btor (btor);
  clone->options.beta_reduce_all.val = 1;
  clone->options.verbosity.val       = 0;
#ifndef NBTORLOG
  clone->options.loglevel.val = 0;
#endif

  res           = btor_simplify (clone);
  num_ops_orig  = sum_ops (btor);
  num_ops_clone = sum_ops (clone);
  BTOR_MSG (btor->msg,
            1,
            "  number of nodes: %d/%d (factor: %.1f, max: %d)",
            num_ops_orig,
            num_ops_clone,
            (float) num_ops_clone / num_ops_orig,
            btor->options.pbra_ops_factor.val);

  if (res != BTOR_UNKNOWN)
  {
    delta = btor_time_stamp () - start;
    BTOR_MSG (btor->msg, 1, "  simplified in %.2f seconds", delta);
    btor->time.br_probing += delta;
    btor_delete_btor (clone);
    return res;
  }
  else if (num_ops_clone < num_ops_orig * btor->options.pbra_ops_factor.val)
  {
    BTOR_MSG (btor->msg,
              1,
              "  limit refinement iterations to 10 and SAT conflicts to %d",
              btor->options.pbra_sat_limit.val);
    res = clone->slv->api.sat (clone,
                               btor->options.pbra_lod_limit.val,
                               btor->options.pbra_sat_limit.val);
    btor_delete_btor (clone);
  }

  if (res != BTOR_UNKNOWN)
  {
    delta = btor_time_stamp () - start;
    BTOR_MSG (btor->msg, 1, "  probing succeeded (%.2f seconds)", delta);
    btor->time.br_probing += delta;
    return res;
  }

  delta = btor_time_stamp () - start;
  BTOR_MSG (btor->msg, 1, "  probing did not succeed (%.2f seconds)", delta);
  btor->time.br_probing += delta;

  return BTOR_UNKNOWN;
}
#endif

int
btor_sat_btor (Btor *btor, int lod_limit, int sat_limit)
{
  assert (btor);
  assert (btor->btor_sat_btor_called >= 0);
  assert (btor->options.incremental.val || btor->btor_sat_btor_called == 0);

  int res;

  if (!btor->slv) btor->slv = new_core_solver (btor);
  assert (btor->slv);

#ifdef BTOR_ENABLE_BETA_REDUCTION_PROBING
  if (btor->slv->kind == BTOR_CORE_SOLVER_KIND
      && btor_has_clone_support_sat_mgr (btor_get_sat_mgr_btor (btor))
      && btor->options.probe_beta_reduce_all.val && lod_limit == -1
      && sat_limit == -1)
  {
    res = br_probe (btor);
    if (res != BTOR_UNKNOWN) return res;
  }
#endif

#ifdef BTOR_CHECK_UNCONSTRAINED
  Btor *uclone = 0;
  if (btor_has_clone_support_sat_mgr (btor_get_sat_mgr_btor (btor))
      && btor->options.ucopt.val && btor->options.rewrite_level.val > 2
      && !btor->options.incremental.val && !btor->options.model_gen.val)
  {
    uclone                           = btor_clone_btor (btor);
    uclone->options.auto_cleanup.val = 1;
    uclone->options.ucopt.val        = 0;
  }
#endif

#ifdef BTOR_CHECK_MODEL
  Btor *mclone                     = 0;
  BtorPtrHashTable *inputs         = 0;
  mclone                           = btor_clone_exp_layer (btor, 0);
  mclone->options.loglevel.val     = 0;
  mclone->options.verbosity.val    = 0;
  mclone->options.dual_prop.val    = 0;
  inputs                           = map_inputs_check_model (btor, mclone);
  mclone->options.auto_cleanup.val = 1;
#endif

#ifdef BTOR_CHECK_DUAL_PROP
  Btor *dpclone = 0;
  if (btor_has_clone_support_sat_mgr (btor_get_sat_mgr_btor (btor))
      && btor->options.dual_prop.val)
  {
    dpclone                                    = btor_clone_btor (btor);
    dpclone->options.loglevel.val              = 0;
    dpclone->options.verbosity.val             = 0;
    dpclone->options.auto_cleanup.val          = 1;
    dpclone->options.auto_cleanup_internal.val = 1;
    dpclone->options.dual_prop.val             = 0;
  }
#endif

  res = btor->slv->api.sat (btor, lod_limit, sat_limit);
  btor->btor_sat_btor_called++;

#ifdef BTOR_CHECK_UNCONSTRAINED
  if (uclone)
  {
    assert (btor->options.ucopt.val);
    assert (btor->options.rewrite_level.val > 2);
    assert (!btor->options.incremental.val);
    assert (!btor->options.model_gen.val);
    int ucres = uclone->slv->api.sat (uclone, lod_limit, sat_limit);
    assert (res == ucres);
  }
#endif

  if (btor->options.model_gen.val && res == BTOR_SAT)
    btor->slv->api.generate_model (btor, btor->options.model_gen.val == 2, 1);

#ifdef BTOR_CHECK_MODEL
  if (mclone)
  {
    assert (inputs);
    if (res == BTOR_SAT && !btor->options.ucopt.val)
    {
      if (!btor->options.model_gen.val)
        btor->slv->api.generate_model (btor, 0, 1);
      check_model (btor, mclone, inputs);
      if (!btor->options.model_gen.val) btor_delete_model (btor);
    }

    BtorHashTableIterator it;
    btor_init_node_hash_table_iterator (&it, inputs);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      btor_release_exp (btor, (BtorNode *) it.bucket->data.asPtr);
      btor_release_exp (mclone, btor_next_node_hash_table_iterator (&it));
    }
    btor_delete_ptr_hash_table (inputs);
    btor_delete_btor (mclone);
  }
#endif

#ifdef BTOR_CHECK_DUAL_PROP
  if (dpclone && btor->options.dual_prop.val)
  {
    check_dual_prop (btor, dpclone);
    btor_delete_btor (dpclone);
  }
#endif
  return res;
}

static int
is_valid_argument (Btor *btor, BtorNode *exp)
{
  exp = BTOR_REAL_ADDR_NODE (exp);
  if (btor_is_fun_exp (btor, exp)) return 0;
  if (btor_is_array_exp (btor, exp)) return 0;
  /* scope of bound parmaters already closed (cannot be used anymore) */
  if (BTOR_IS_PARAM_NODE (exp) && btor_param_is_bound (exp)) return 0;
  return 1;
}

int
btor_fun_sort_check (Btor *btor, uint32_t argc, BtorNode **args, BtorNode *fun)
{
  (void) btor;
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (btor_is_fun_exp (btor, fun));
  assert (argc == btor_get_fun_arity (btor, fun));

  uint32_t i;
  int pos = -1;
  BtorSortId sort;
  BtorSortUniqueTable *sorts;
  BtorTupleSortIterator it;

  sorts = &btor->sorts_unique_table;
  assert (btor_is_tuple_sort (sorts,
                              btor_get_domain_fun_sort (sorts, fun->sort_id)));
  btor_init_tuple_sort_iterator (
      &it, sorts, btor_get_domain_fun_sort (sorts, fun->sort_id));
  for (i = 0; i < argc; i++)
  {
    assert (btor_has_next_tuple_sort_iterator (&it));
    sort = btor_next_tuple_sort_iterator (&it);
    /* NOTE: we do not allow functions or arrays as arguments yet */
    if (!is_valid_argument (btor, args[i])
        || sort != BTOR_REAL_ADDR_NODE (args[i])->sort_id)
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

  synthesize_exp (btor, exp, 0);
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

  synthesize_exp (btor, exp, backannotation);
  result = BTOR_REAL_ADDR_NODE (exp)->av;
  assert (result);

  if (BTOR_IS_INVERTED_NODE (exp))
    result = btor_not_aigvec (avmgr, result);
  else
    result = btor_copy_aigvec (avmgr, result);

  return result;
}

BtorBitVector *
btor_eval_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (exp);
  assert (btor->bv_model);

  int i;
  double start;
  BtorMemMgr *mm;
  BtorNodePtrStack work_stack;
  BtorVoidPtrStack arg_stack;
  BtorNode *cur, *real_cur, *next;
  BtorPtrHashTable *cache;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorBitVector *result = 0, *inv_result, **e;
  BtorCoreSolver *slv;

  start = btor_time_stamp ();
  mm    = btor->mm;
  slv   = BTOR_CORE_SOLVER (btor);
  slv->stats.eval_exp_calls++;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (arg_stack);
  cache = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_PUSH_STACK (mm, work_stack, exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->eval_mark);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur      = BTOR_POP_STACK (work_stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!real_cur->simplified);

    if (real_cur->eval_mark == 0)
    {
      if (BTOR_IS_BV_VAR_NODE (real_cur) || BTOR_IS_APPLY_NODE (real_cur)
          || BTOR_IS_FEQ_NODE (real_cur) || has_bv_assignment (btor, real_cur))
      {
        result = get_bv_assignment (btor, real_cur);
        goto EVAL_EXP_PUSH_RESULT;
      }
      else if (BTOR_IS_BV_CONST_NODE (real_cur))
      {
        result = btor_copy_bv (btor->mm, btor_const_get_bits (real_cur));
        goto EVAL_EXP_PUSH_RESULT;
      }
      /* substitute param with its assignment */
      else if (BTOR_IS_PARAM_NODE (real_cur))
      {
        next = btor_param_cur_assignment (real_cur);
        assert (next);
        if (BTOR_IS_INVERTED_NODE (cur)) next = BTOR_INVERT_NODE (next);
        BTOR_PUSH_STACK (mm, work_stack, next);
        continue;
      }

      BTOR_PUSH_STACK (mm, work_stack, cur);
      real_cur->eval_mark = 1;

      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, work_stack, real_cur->e[i]);
    }
    else if (real_cur->eval_mark == 1)
    {
      assert (!BTOR_IS_PARAM_NODE (real_cur));
      assert (!BTOR_IS_ARGS_NODE (real_cur));
      assert (!BTOR_IS_FUN_NODE (real_cur));
      assert (real_cur->arity >= 1);
      assert (real_cur->arity <= 3);
      assert (real_cur->arity <= BTOR_COUNT_STACK (arg_stack));

      real_cur->eval_mark = 2;
      arg_stack.top -= real_cur->arity;
      e = (BtorBitVector **) arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result = btor_slice_bv (mm,
                                  e[0],
                                  btor_slice_get_upper (real_cur),
                                  btor_slice_get_lower (real_cur));
          btor_free_bv (mm, e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_BEQ_NODE:
          result = btor_eq_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_BCOND_NODE:
          if (btor_is_true_bv (e[2]))
            result = btor_copy_bv (mm, e[1]);
          else
            result = btor_copy_bv (mm, e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          btor_free_bv (mm, e[2]);
          break;
        default:
          BTORLOG (1, "  *** %s", node2string (real_cur));
          /* should be unreachable */
          assert (0);
      }

      assert (!btor_find_in_ptr_hash_table (cache, real_cur));
      btor_insert_in_ptr_hash_table (cache, real_cur)->data.asPtr =
          btor_copy_bv (mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_bv (mm, result);
        btor_free_bv (mm, result);
        result = inv_result;
      }

      BTOR_PUSH_STACK (mm, arg_stack, result);
    }
    else
    {
      assert (real_cur->eval_mark == 2);
      b = btor_find_in_ptr_hash_table (cache, real_cur);
      assert (b);
      result = btor_copy_bv (mm, (BtorBitVector *) b->data.asPtr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur            = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));
    cur->eval_mark = 0;
  }

  while (!BTOR_EMPTY_STACK (arg_stack))
  {
    inv_result = BTOR_POP_STACK (arg_stack);
    btor_free_bv (mm, inv_result);
  }

  btor_init_node_hash_table_iterator (&it, cache);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    btor_free_bv (mm, (BtorBitVector *) it.bucket->data.asPtr);
    real_cur            = btor_next_node_hash_table_iterator (&it);
    real_cur->eval_mark = 0;
  }

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  btor_delete_ptr_hash_table (cache);

  //  BTORLOG ("%s: %s '%s'", __FUNCTION__, node2string (exp), result);
  slv->time.eval += btor_time_stamp () - start;

  return result;
}

void
btor_release_bv_assignment_str (Btor *btor, char *assignment)
{
  assert (btor);
  assert (assignment);
  btor_freestr (btor->mm, assignment);
}

#ifdef BTOR_CHECK_MODEL
BtorPtrHashTable *
map_inputs_check_model (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);

  BtorNode *cur;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorPtrHashTable *inputs;

  inputs = btor_new_ptr_hash_table (clone->mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

  update_reachable (clone, 1);

  btor_init_node_hash_table_iterator (&it, clone->bv_vars);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    if (!cur->reachable) continue;
    b = btor_find_in_ptr_hash_table (btor->bv_vars, cur);
    assert (b);

    assert (!btor_find_in_ptr_hash_table (inputs, cur));
    btor_insert_in_ptr_hash_table (inputs, btor_copy_exp (clone, cur))
        ->data.asPtr = btor_copy_exp (btor, (BtorNode *) b->key);
  }

  btor_init_node_hash_table_iterator (&it, clone->ufs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    if (!cur->reachable) continue;
    b = btor_find_in_ptr_hash_table (btor->ufs, cur);
    assert (b);

    assert (!btor_find_in_ptr_hash_table (inputs, cur));
    btor_insert_in_ptr_hash_table (inputs, btor_copy_exp (clone, cur))
        ->data.asPtr = btor_copy_exp (btor, (BtorNode *) b->key);
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
  btor->options.rewrite_level.val = rewrite_level;

  t = btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);

  /* collect all leaves and rebuild whole formula */
  for (i = BTOR_COUNT_STACK (btor->nodes_id_table) - 1; i >= 0; i--)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;

    if (BTOR_IS_PROXY_NODE (cur)) continue;

    if (cur->arity == 0)
    {
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_BV_CONST_NODE (cur)
              || BTOR_IS_PARAM_NODE (cur) || BTOR_IS_UF_NODE (cur));
      btor_insert_in_ptr_hash_table (t, cur);
    }
  }

  substitute_and_rebuild (btor, t, 0);
  btor_delete_ptr_hash_table (t);
}

static void
check_model (Btor *btor, Btor *clone, BtorPtrHashTable *inputs)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_SAT);
  assert (clone);
  assert (inputs);

  uint32_t i;
  int ret;
  BtorNode *cur, *exp, *simp, *real_simp, *model, *eq, *args, *apply;
  BtorHashTableIterator it;
  const BtorPtrHashTable *fmodel;
  BtorBitVector *value;
  BtorBitVectorTuple *args_tuple;
  BtorNodePtrStack consts;

  /* formula did not change since last sat call, we have to reset assumptions
   * from the previous run */
  if (clone->valid_assignments) reset_incremental_usage (clone);

  /* add assumptions as assertions */
  btor_init_node_hash_table_iterator (&it, clone->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_assert_exp (clone, btor_next_node_hash_table_iterator (&it));
  btor_reset_assumptions (clone);

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0) substitute_var_exps (clone);

  /* rebuild formula with new rewriting level */
  rebuild_formula (clone, 3);

  /* add bit vector variable models */
  BTOR_INIT_STACK (consts);
  btor_init_node_hash_table_iterator (&it, inputs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    exp = (BtorNode *) it.bucket->data.asPtr;
    assert (exp);
    assert (BTOR_IS_REGULAR_NODE (exp));
    assert (exp->btor == btor);
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->btor == clone);
    simp      = btor_simplify_exp (clone, cur);
    real_simp = BTOR_REAL_ADDR_NODE (simp);

    if (BTOR_IS_FUN_NODE (real_simp))
    {
      fmodel = btor_get_fun_model (btor, exp);
      if (!fmodel) continue;

      BTORLOG (2, "assert model for %s", node2string (real_simp));
      btor_init_hash_table_iterator (&it, (BtorPtrHashTable *) fmodel);
      while (btor_has_next_hash_table_iterator (&it))
      {
        value      = (BtorBitVector *) it.bucket->data.asPtr;
        args_tuple = btor_next_hash_table_iterator (&it);

        /* create condition */
        assert (BTOR_EMPTY_STACK (consts));
        for (i = 0; i < args_tuple->arity; i++)
        {
          model = btor_const_exp (clone, args_tuple->bv[i]);
          BTOR_PUSH_STACK (clone->mm, consts, model);
        }

        args  = btor_args_exp (clone, BTOR_COUNT_STACK (consts), consts.start);
        apply = btor_apply_exp (clone, real_simp, args);
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
               node2string (real_simp),
               btor_get_symbol_exp (clone, cur));
      /* we need to invert the assignment if simplified is inverted */
      model = btor_const_exp (clone,
                              (BtorBitVector *) btor_get_bv_model (
                                  btor, BTOR_COND_INVERT_NODE (simp, exp)));
      eq    = btor_eq_exp (clone, real_simp, model);
      btor_assert_exp (clone, eq);
      btor_release_exp (clone, eq);
      btor_release_exp (clone, model);
    }
  }
  BTOR_RELEASE_STACK (clone->mm, consts);

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0) substitute_var_exps (clone);

  clone->options.beta_reduce_all.val = 1;
  ret                                = btor_simplify (clone);

  //  btor_print_model (btor, "btor", stdout);
  assert (ret != BTOR_UNKNOWN
          || clone->slv->api.sat (clone, -1, -1) == BTOR_SAT);
  // TODO: check if roots have been simplified through aig rewriting
  // BTOR_ABORT_CORE (ret == BTOR_UNKNOWN, "rewriting needed");
  BTOR_ABORT_CORE (ret == BTOR_UNSAT, "invalid model");
}
#endif

#ifdef BTOR_CHECK_FAILED
static void
check_failed_assumptions (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_UNSAT);

  BtorNode *ass;
  BtorHashTableIterator it;

  /* assert failed assumptions */
  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    ass = btor_next_node_hash_table_iterator (&it);
    if (btor_failed_exp (btor, ass))
    {
      ass = btor_match_node (clone, ass);
      assert (ass);
      btor_assert_exp (clone, ass);
    }
  }

  /* cleanup assumptions */
  btor_init_node_hash_table_iterator (&it, clone->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (clone, btor_next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (clone->assumptions);
  clone->assumptions =
      btor_new_ptr_hash_table (clone->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);

  assert (clone->slv->api.sat (clone, -1, -1) == BTOR_UNSAT);
}
#endif

#ifdef BTOR_CHECK_DUAL_PROP
static void
check_dual_prop (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (btor->options.dual_prop.val);
  assert (clone);

  clone->slv->api.sat (clone, -1, -1);
  assert (btor->last_sat_result == clone->last_sat_result);
}
#endif

/*------------------------------------------------------------------------*/

static void *
clone_core_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (exp_map);

  int h;
  BtorCoreSolver *slv;
  BtorCoreSolver *res;

  if (!(slv = BTOR_CORE_SOLVER (btor))) return 0;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorCoreSolver));

  res->lemmas = btor_clone_ptr_hash_table (
      clone->mm, slv->lemmas, btor_clone_key_as_node, 0, exp_map, 0);

  btor_clone_node_ptr_stack (
      clone->mm, &slv->cur_lemmas, &res->cur_lemmas, exp_map);

  if (slv->score)
  {
    h = btor->options.just_heuristic.val;
    if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
    {
      res->score = btor_clone_ptr_hash_table (clone->mm,
                                              slv->score,
                                              btor_clone_key_as_node,
                                              btor_clone_data_as_htable_ptr,
                                              exp_map,
                                              exp_map);
    }
    else
    {
      assert (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP);
      res->score = btor_clone_ptr_hash_table (clone->mm,
                                              slv->score,
                                              btor_clone_key_as_node,
                                              btor_clone_data_as_int,
                                              exp_map,
                                              0);
    }
  }

  BTOR_INIT_STACK (res->stats.lemmas_size);
  if (BTOR_SIZE_STACK (slv->stats.lemmas_size) > 0)
  {
    BTOR_CNEWN (clone->mm,
                res->stats.lemmas_size.start,
                BTOR_SIZE_STACK (slv->stats.lemmas_size));

    res->stats.lemmas_size.end =
        res->stats.lemmas_size.start + BTOR_SIZE_STACK (slv->stats.lemmas_size);
    res->stats.lemmas_size.top = res->stats.lemmas_size.start
                                 + BTOR_COUNT_STACK (slv->stats.lemmas_size);
    memcpy (res->stats.lemmas_size.start,
            slv->stats.lemmas_size.start,
            BTOR_SIZE_STACK (slv->stats.lemmas_size) * sizeof (int));
  }

  return res;
}

static void
delete_core_solver (Btor *btor)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  BtorCoreSolver *slv;
  BtorPtrHashTable *t;
  BtorHashTableIterator it, iit;
  BtorNode *exp;

  if (!(slv = BTOR_CORE_SOLVER (btor))) return;

  btor_init_node_hash_table_iterator (&it, slv->lemmas);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (slv->lemmas);

  if (slv->score)
  {
    btor_init_node_hash_table_iterator (&it, slv->score);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      if (btor->options.just_heuristic.val == BTOR_JUST_HEUR_BRANCH_MIN_APP)
      {
        t   = (BtorPtrHashTable *) it.bucket->data.asPtr;
        exp = btor_next_node_hash_table_iterator (&it);
        btor_release_exp (btor, exp);

        btor_init_node_hash_table_iterator (&iit, t);
        while (btor_has_next_node_hash_table_iterator (&iit))
          btor_release_exp (btor, btor_next_node_hash_table_iterator (&iit));
        btor_delete_ptr_hash_table (t);
      }
      else
      {
        assert (btor->options.just_heuristic.val
                == BTOR_JUST_HEUR_BRANCH_MIN_DEP);
        btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
      }
    }
    btor_delete_ptr_hash_table (slv->score);
  }

  BTOR_RELEASE_STACK (btor->mm, slv->cur_lemmas);
  BTOR_RELEASE_STACK (btor->mm, slv->stats.lemmas_size);
  BTOR_DELETE (btor->mm, slv);
  btor->slv = 0;
}

static int
sat_core_solver (Btor *btor, int lod_limit, int sat_limit)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  BtorCoreSolver *slv;
  double start;
  int i, sat_result;
  BtorSATMgr *smgr;
  Btor *clone;
  BtorNode *clone_root, *lemma;
  BtorNodeMap *exp_map;
  int simp_sat_result;
#ifdef BTOR_CHECK_FAILED
  Btor *faclone = 0;
#endif

  start = btor_time_stamp ();
  slv   = BTOR_CORE_SOLVER (btor);
  assert (slv);

  clone      = 0;
  clone_root = 0;
  exp_map    = 0;

  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_UNKNOWN;
    goto DONE;
  }

  simp_sat_result = btor_simplify (btor);
  update_assumptions (btor);

#ifdef BTOR_CHECK_FAILED
  if (btor_has_clone_support_sat_mgr (btor_get_sat_mgr_btor (btor))
      && btor->options.chk_failed_assumptions.val)
  {
    faclone                           = btor_clone_btor (btor);
    faclone->options.auto_cleanup.val = 1;
#ifdef BTOR_CHECK_MODEL
    /* cleanup dangling references when model validation is enabled */
    faclone->options.auto_cleanup_internal.val = 1;
#endif
    faclone->options.loglevel.val               = 0;
    faclone->options.verbosity.val              = 0;
    faclone->options.chk_failed_assumptions.val = 0;
    faclone->options.dual_prop.val              = 0;  // FIXME necessary?
  }
#endif

  if (btor->inconsistent) goto UNSAT;

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_UNKNOWN;
    goto DONE;
  }

  smgr = btor_get_sat_mgr_btor (btor);

  if (!btor_is_initialized_sat (smgr)) btor_init_sat (smgr);

  /* reset SAT solver to non-incremental if all functions have been
   * eliminated */
  if (!btor->options.incremental.val && smgr->inc_required
      && btor->lambdas->count == 0 && btor->ufs->count == 0)
  {
    smgr->inc_required = 0;
    BTOR_MSG (btor->msg,
              1,
              "no functions found, resetting SAT solver to non-incremental");
  }

  if (btor->valid_assignments == 1) reset_incremental_usage (btor);

  if (btor->feqs->count > 0)
  {
    update_reachable (btor, 1);
    add_function_inequality_constraints (btor);
  }

  process_unsynthesized_constraints (btor);
  if (btor->found_constraint_false)
  {
  UNSAT:
    sat_result = BTOR_UNSAT;
    goto DONE;
  }
  assert (btor->unsynthesized_constraints->count == 0);
  assert (check_all_hash_tables_proxy_free_dbg (btor));
  assert (check_all_hash_tables_simp_free_dbg (btor));

#ifndef NDEBUG
  BtorHashTableIterator it;
  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    assert (!BTOR_REAL_ADDR_NODE (btor_next_node_hash_table_iterator (&it))
                 ->simplified);
#endif

  update_reachable (btor, 0);
  assert (check_reachable_flag_dbg (btor));

  add_again_assumptions (btor);
  assert (check_reachable_flag_dbg (btor));

  if (sat_limit > -1)
    sat_result = timed_sat_sat (btor, sat_limit);
  else
    sat_result = timed_sat_sat (btor, -1);

  if (btor->options.dual_prop.val && sat_result == BTOR_SAT
      && simp_sat_result != BTOR_SAT)
  {
    clone = new_exp_layer_clone_for_dual_prop (btor, &exp_map, &clone_root);
  }

  while (sat_result == BTOR_SAT)
  {
    if (btor_terminate_btor (btor)
        || (lod_limit > -1 && slv->stats.lod_refinements >= lod_limit))
    {
      sat_result = BTOR_UNKNOWN;
      goto DONE;
    }

    check_and_resolve_conflicts (btor, clone, clone_root, exp_map);

    if (BTOR_EMPTY_STACK (slv->cur_lemmas)) break;
    slv->stats.refinement_iterations++;

    BTORLOG (1, "add %d lemma(s)", BTOR_COUNT_STACK (slv->cur_lemmas));
    /* add generated lemmas to formula */
    for (i = 0; i < BTOR_COUNT_STACK (slv->cur_lemmas); i++)
    {
      lemma = BTOR_PEEK_STACK (slv->cur_lemmas, i);
      assert (!BTOR_REAL_ADDR_NODE (lemma)->simplified);
      insert_unsynthesized_constraint (btor, lemma);
      mark_reachable (btor, lemma);
      if (clone)
        add_lemma_to_dual_prop_clone (btor, clone, &clone_root, lemma, exp_map);
    }
    BTOR_RESET_STACK (slv->cur_lemmas);

    if (btor->options.verbosity.val)
    {
      fprintf (stdout,
               "\r[btorcore] %d iterations, %d lemmas, %d ext. lemmas, "
               "vars %d, applies %d\r",
               slv->stats.refinement_iterations,
               slv->stats.lod_refinements,
               slv->stats.extensionality_lemmas,
               btor->ops[BTOR_BV_VAR_NODE].cur,
               btor->ops[BTOR_APPLY_NODE].cur);
      fflush (stdout);
    }

    /* may be set via insert_unsythesized_constraint
     * in case generated lemma is false */
    if (btor->inconsistent) goto UNSAT;

    process_unsynthesized_constraints (btor);
    if (btor->found_constraint_false) goto UNSAT;
    assert (btor->unsynthesized_constraints->count == 0);
    assert (check_all_hash_tables_proxy_free_dbg (btor));
    assert (check_all_hash_tables_simp_free_dbg (btor));
    assert (check_reachable_flag_dbg (btor));
    add_again_assumptions (btor);
    sat_result = timed_sat_sat (btor, -1);
  }

DONE:
  if (btor->options.verbosity.val && slv->stats.lod_refinements > 0)
    fprintf (stdout, "\n");

  btor->valid_assignments = 1;
  btor->last_sat_result   = sat_result;

  if (clone)
  {
    assert (exp_map);
    btor_delete_node_map (exp_map);
    btor_release_exp (clone, clone_root);
    btor_delete_btor (clone);
  }
#ifdef BTOR_CHECK_FAILED
  if (faclone && btor->options.chk_failed_assumptions.val)
  {
    if (!btor->inconsistent && btor->last_sat_result == BTOR_UNSAT)
      check_failed_assumptions (btor, faclone);
    btor_delete_btor (faclone);
  }
#endif
  BTOR_MSG (btor->msg,
            1,
            "SAT call %d returned %d in %.3f seconds",
            btor->btor_sat_btor_called + 1,
            sat_result,
            btor_time_stamp () - start);
  return sat_result;
}

static void
generate_model_core_solver (Btor *btor, int model_for_all_nodes, int reset)
{
  assert (btor);
  /* already created during check_and_resolve_conflicts */
  assert (btor->bv_model);

  (void) reset;
  btor_init_fun_model (btor, &btor->fun_model);

  btor_generate_model (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

static void
print_stats_core_solver (Btor *btor)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  int i;
  BtorCoreSolver *slv;

  if (!(slv = BTOR_CORE_SOLVER (btor))) return;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "lemmas on demand statistics:");
  BTOR_MSG (btor->msg,
            1,
            " refinement iterations: %d",
            slv->stats.refinement_iterations);
  BTOR_MSG (btor->msg, 1, " LOD refinements: %d", slv->stats.lod_refinements);
  if (slv->stats.lod_refinements)
  {
    BTOR_MSG (btor->msg,
              1,
              " function congruence conflicts: %d",
              slv->stats.function_congruence_conflicts);
    BTOR_MSG (btor->msg,
              1,
              " beta reduction conflicts: %d",
              slv->stats.beta_reduction_conflicts);
    BTOR_MSG (btor->msg,
              1,
              " extensionality lemmas: %d",
              slv->stats.extensionality_lemmas);
    BTOR_MSG (btor->msg,
              1,
              " average lemma size: %.1f",
              BTOR_AVERAGE_UTIL (slv->stats.lemmas_size_sum,
                                 slv->stats.lod_refinements));
    for (i = 1; i < BTOR_SIZE_STACK (slv->stats.lemmas_size); i++)
    {
      if (!slv->stats.lemmas_size.start[i]) continue;
      BTOR_MSG (btor->msg,
                1,
                "   lemmas of size %d: %d",
                i,
                slv->stats.lemmas_size.start[i]);
    }
  }

  BTOR_MSG (
      btor->msg, 1, "expression evaluations: %lld", slv->stats.eval_exp_calls);
  BTOR_MSG (btor->msg, 1, "propagations: %lld", slv->stats.propagations);
  BTOR_MSG (
      btor->msg, 1, "propagations down: %lld", slv->stats.propagations_down);
  BTOR_MSG (btor->msg,
            1,
            "partial beta reduction restarts: %lld",
            slv->stats.partial_beta_reduction_restarts);

  if (btor->options.dual_prop.val)
  {
    BTOR_MSG (btor->msg,
              1,
              "dual prop. vars (failed/assumed): %d/%d",
              slv->stats.dp_failed_vars,
              slv->stats.dp_assumed_vars);
    BTOR_MSG (btor->msg,
              1,
              "dual prop. applies (failed/assumed): %d/%d",
              slv->stats.dp_failed_applies,
              slv->stats.dp_assumed_applies);
  }
}

static void
print_time_stats_core_solver (Btor *btor)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  BtorCoreSolver *slv;

  if (!(slv = BTOR_CORE_SOLVER (btor))) return;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "%.2f seconds expression evaluation", slv->time.eval);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds initial applies search",
            slv->time.search_init_apps);

  if (btor->options.just.val || btor->options.dual_prop.val)
  {
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds compute scores for initial applies search",
              slv->time.search_init_apps_compute_scores);
    BTOR_MSG (
        btor->msg,
        1,
        "%.2f seconds merge applies in compute scores for init apps search",
        slv->time.search_init_apps_compute_scores_merge_applies);
  }

  if (btor->options.dual_prop.val)
  {
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds cloning for initial applies search",
              slv->time.search_init_apps_cloning);
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds SAT solving for initial applies search",
              slv->time.search_init_apps_sat);
    BTOR_MSG (
        btor->msg,
        1,
        "%.2f seconds collecting bv vars and apps for initial applies search",
        slv->time.search_init_apps_collect_var_apps);
    BTOR_MSG (
        btor->msg,
        1,
        "%.2f seconds collecting initial applies via failed assumptions (FA)",
        slv->time.search_init_apps_collect_fa);
    BTOR_MSG (
        btor->msg,
        1,
        "%.2f seconds cone traversal when collecting initial applies via FA",
        slv->time.search_init_apps_collect_fa_cone);
  }

  BTOR_MSG (btor->msg, 1, "%.2f seconds lemma generation", slv->time.lemma_gen);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds not encoded apply search",
            slv->time.find_nenc_app);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds propagation apply search",
            slv->time.find_prop_app);

  if (btor->options.dual_prop.val)
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds propagation apply in conds search",
              slv->time.find_cond_prop_app);

  BTOR_MSG (btor->msg, 1, "%.2f seconds in pure SAT solving", slv->time.sat);
  BTOR_MSG (btor->msg, 1, "");
}

BtorSolver *
new_core_solver (Btor *btor)
{
  assert (btor);

  BtorCoreSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind                 = BTOR_CORE_SOLVER_KIND;
  slv->api.clone            = clone_core_solver;
  slv->api.delet            = delete_core_solver;
  slv->api.sat              = sat_core_solver;
  slv->api.generate_model   = generate_model_core_solver;
  slv->api.print_stats      = print_stats_core_solver;
  slv->api.print_time_stats = print_time_stats_core_solver;

  slv->lemmas = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (slv->cur_lemmas);

  BTOR_INIT_STACK (slv->stats.lemmas_size);

  BTOR_MSG (btor->msg, 1, "enabled core engine");

  return (BtorSolver *) slv;
}

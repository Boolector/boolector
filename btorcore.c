/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"
#include "btorbeta.h"
#include "btorbitvec.h"
#include "btorconfig.h"
#include "btorconst.h"
#include "btorexit.h"
#include "btoriter.h"
#include "btorlog.h"
#include "btormisc.h"
#include "btorparamcache.h"
#include "btorrewrite.h"
#include "btorsat.h"
#include "btorutil.h"

#include <limits.h>

/*------------------------------------------------------------------------*/

// #define BTOR_DO_NOT_ELIMINATE_SLICES

#ifndef BTOR_USE_LINGELING
#define BTOR_DO_NOT_PROCESS_SKELETON
#endif

#define ENABLE_APPLY_PROP_DOWN 1

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

//#define MARK_PROP_UP(exp) ((BtorNode *) (1ul | (unsigned long int) (exp)))
//#define PROPAGATED_UPWARDS(exp) (1ul & (unsigned long int) (exp)->parent)

/*------------------------------------------------------------------------*/

const char *const g_btor_op2string[] = {
    "invalid", "const", "var",    "array", "param", "slice",  "and",
    "beq",     "aeq",   "add",    "mul",   "ult",   "sll",    "srl",
    "udiv",    "urem",  "concat", "read",  "apply", "lambda", "write",
    "bcond",   "acond", "args",   "proxy"};

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/
static int
check_unique_table_children_proxy_free_dbg (const Btor *btor)
{
  int i, j;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      for (j = 0; j < cur->arity; j++)
        if (BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (cur->e[j]))) return 0;
  return 1;
}

static int
check_unique_table_mark_unset_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      if (cur->mark != 0) return 0;
  return 1;
}

static int
check_unique_table_aux_mark_unset_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      if (cur->aux_mark != 0) return 0;
  return 1;
}

static int
check_hash_table_proxy_free_dbg (const BtorPtrHashTable *table)
{
  BtorPtrHashBucket *b;
  for (b = table->first; b; b = b->next)
    if (BTOR_REAL_ADDR_NODE (b->key)->kind == BTOR_PROXY_NODE) return 0;
  return 1;
}

static int
check_all_hash_tables_proxy_free_dbg (const Btor *btor)
{
  if (!check_hash_table_proxy_free_dbg (btor->varsubst_constraints)) return 0;
  if (!check_hash_table_proxy_free_dbg (btor->embedded_constraints)) return 0;
  if (!check_hash_table_proxy_free_dbg (btor->unsynthesized_constraints))
    return 0;
  if (!check_hash_table_proxy_free_dbg (btor->synthesized_constraints))
    return 0;
  return 1;
}

static int
check_hash_table_simp_free_dbg (const BtorPtrHashTable *table,
                                const char *table_name)
{
  BtorPtrHashBucket *b;
  (void) table_name;
  for (b = table->first; b; b = b->next)
    if (BTOR_REAL_ADDR_NODE (b->key)->simplified) return 0;
  return 1;
}

static int
check_all_hash_tables_simp_free_dbg (const Btor *btor)
{
  if (!check_hash_table_simp_free_dbg (btor->varsubst_constraints,
                                       "varsubst_constraints"))
    return 0;
  if (!check_hash_table_simp_free_dbg (btor->embedded_constraints,
                                       "embedded_constraints"))
    return 0;
  if (!check_hash_table_simp_free_dbg (btor->unsynthesized_constraints,
                                       "unsynthesized_constraints"))
    return 0;
  if (!check_hash_table_simp_free_dbg (btor->synthesized_constraints,
                                       "synthesized_constraints"))
    return 0;
  return 1;
}
/*------------------------------------------------------------------------*/
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

#if 0
static void
btor_init_substitutions (Btor * btor)
{
  assert (btor);
  assert (!btor->substitutions);

  btor->substitutions =
    btor_new_ptr_hash_table (btor->mm,
			     (BtorHashPtr) btor_hash_exp_by_id,
			     (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
btor_delete_substitutions (Btor * btor)
{
  assert (btor);

  BtorPtrHashBucket *b;

  for (b = btor->substitutions->first; b; b = b->next)
    {
      btor_release_exp (btor, (BtorNode *) b->data.asPtr);
      btor_release_exp (btor, (BtorNode *) b->key);
    }

  btor_delete_ptr_hash_table (btor->substitutions);
  btor->substitutions = 0;
}

static void
btor_insert_substitution (Btor * btor, BtorNode * exp, BtorNode * subst,
			  int update)
{
  assert (btor);
  assert (exp);
  assert (subst);
  assert (btor->substitutions);
  assert (update == 0 || update == 1);

  BtorPtrHashBucket *b;
  exp = BTOR_REAL_ADDR_NODE (exp);

  assert (update || !btor_find_in_ptr_hash_table (btor->substitutions, exp)); 

  if (update && (b = btor_find_in_ptr_hash_table (btor->substitutions, exp)))
    {
      assert (b->data.asPtr);
      /* release data of current bucket */
      btor_release_exp (btor, (BtorNode *) b->data.asPtr);
      btor_remove_from_ptr_hash_table (btor->substitutions, exp, 0, 0);
      /* release key of current bucket */
      btor_release_exp (btor, exp);
    }

  btor_insert_in_ptr_hash_table (btor->substitutions,
    btor_copy_exp (btor, exp))->data.asPtr = btor_copy_exp (btor, subst);
}

#endif

static BtorNode *
btor_find_substitution (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *result;
  BtorPtrHashBucket *bucket;

  if (!btor->substitutions) return 0;

  bucket = btor_find_in_ptr_hash_table (btor->substitutions,
                                        BTOR_REAL_ADDR_NODE (exp));

  if (!bucket) return 0;

  result = btor_simplify_exp (btor, (BtorNode *) bucket->data.asPtr);

  if (BTOR_IS_INVERTED_NODE (exp)) return BTOR_INVERT_NODE (result);
  return result;
}

/*------------------------------------------------------------------------*/

static void
btor_msg (Btor *btor, int level, char *fmt, ...)
{
  va_list ap;
  if (btor->verbosity < level) return;
  fputs ("[btorcore] ", stdout);
  if (btor->inc_enabled && btor->msgtick >= 0)
    printf ("%d : ", (int) btor->msgtick);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
btor_mark_exp (Btor *btor, BtorNode *exp, int new_mark)
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

BtorAIGVecMgr *
btor_get_aigvec_mgr_btor (const Btor *btor)
{
  assert (btor);
  return btor->avmgr;
}

void
btor_set_rewrite_level_btor (Btor *btor, int rewrite_level)
{
  assert (btor);
  assert (btor->rewrite_level >= 0);
  assert (btor->rewrite_level <= 3);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == 2);
  btor->rewrite_level = rewrite_level;
}

void
btor_generate_model_for_all_reads (Btor *btor)
{
  assert (btor);
  btor->generate_model_for_all_reads = 1;
}

int
btor_set_sat_solver (Btor *btor, const char *solver)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;

  assert (btor);
  assert (solver);

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  if (!strcasecmp (solver, "lingeling"))
#ifdef BTOR_USE_LINGELING
  {
    btor_enable_lingeling_sat (smgr, 0, 0);
    return 1;
  }
#else
    return 0;
#endif

  if (!strcasecmp (solver, "minisat"))
#ifdef BTOR_USE_MINISAT
  {
    btor_enable_minisat_sat (smgr);
    return 1;
  }
#else
    return 0;
#endif

  if (!strcasecmp (solver, "picosat"))
#ifdef BTOR_USE_PICOSAT
  {
    btor_enable_picosat_sat (smgr);
    return 1;
  }
#else
    return 0;
#endif

  return 0;
}

void
btor_enable_beta_reduce_all (Btor *btor)
{
  assert (btor);
  btor->beta_reduce_all = 1;
}

void
btor_disable_pretty_print (Btor *btor)
{
  assert (btor);
  btor->pprint = 0;
}

void
btor_enable_model_gen (Btor *btor)
{
  assert (btor);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == 2);
  if (!btor->model_gen)
  {
    btor->model_gen = 1;

    btor->var_rhs =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

    btor->array_rhs =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
  }
}

void
btor_enable_inc_usage (Btor *btor)
{
  assert (btor);
  assert (btor->btor_sat_btor_called == 0);
  btor->inc_enabled = 1;
}

void
btor_set_verbosity_btor (Btor *btor, int verbosity)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;

  assert (btor);
  assert (btor->verbosity >= -1);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == 2);
  btor->verbosity = verbosity;

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);
  btor_set_verbosity_aigvec_mgr (avmgr, verbosity);
  btor_set_verbosity_aig_mgr (amgr, verbosity);
  btor_set_verbosity_sat_mgr (smgr, verbosity);
}

void
btor_set_loglevel_btor (Btor *btor, int loglevel)
{
  assert (btor);
  (void) btor;
  (void) loglevel;
#ifndef NBTORLOG
  btor->loglevel = loglevel;
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
    if (btor->verbosity <= 0) return;

    changes = constraints_stats_changes (btor);

    if (btor->verbosity == 1 && changes < 100000) return;

    if (btor->verbosity == 2 && changes < 1000) return;

    if (btor->verbosity == 3 && changes < 10) return;

    if (!changes) return;
  }

  btor_msg (btor,
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
  for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++) result += btor->ops[i];

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

  assert (btor);

  verbosity = btor->verbosity;

  report_constraint_stats (btor, 1);
  btor_msg (
      btor, 1, "variable substitutions: %d", btor->stats.var_substitutions);
  btor_msg (
      btor, 1, "array substitutions: %d", btor->stats.array_substitutions);
  btor_msg (btor,
            1,
            "embedded constraint substitutions: %d",
            btor->stats.ec_substitutions);
  btor_msg (btor, 1, "assumptions: %u", btor->assumptions->count);
  if (btor->ops[BTOR_AEQ_NODE])
    btor_msg (btor, 1, "virtual reads: %d", btor->stats.vreads);

  if (verbosity > 2)
  {
    btor_msg (btor, 2, "max rec. RW: %d", btor->stats.max_rec_rw_calls);
    btor_msg (btor,
              2,
              "number of expressions ever created: %lld",
              btor->stats.expressions);
    num_final_ops = number_of_ops (btor);
    assert (num_final_ops >= 0);
    btor_msg (btor, 2, "number of final expressions: %d", num_final_ops);
    if (num_final_ops > 0)
      for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++)
        if (btor->ops[i])
          btor_msg (btor, 2, " %s:%d", g_btor_op2string[i], btor->ops[i]);
  }

  btor_msg (btor, 1, "");
  btor_msg (btor, 1, "lemmas on demand statistics:");
  btor_msg (btor, 1, " LOD refinements: %d", btor->stats.lod_refinements);
  if (btor->stats.lod_refinements)
  {
    btor_msg (btor,
              1,
              " array axiom 1 conflicts: %d",
              btor->stats.array_axiom_1_conflicts);
    btor_msg (btor,
              1,
              " array axiom 2 conflicts: %d",
              btor->stats.array_axiom_2_conflicts);
    btor_msg (btor,
              1,
              " average lemma size: %.1f",
              BTOR_AVERAGE_UTIL (btor->stats.lemmas_size_sum,
                                 btor->stats.lod_refinements));
    btor_msg (btor,
              1,
              " average linking clause size: %.1f",
              BTOR_AVERAGE_UTIL (btor->stats.lclause_size_sum,
                                 btor->stats.lod_refinements));
  }
  btor_msg (btor, 1, "");

  btor_msg (
      btor, 1, "linear constraint equations: %d", btor->stats.linear_equations);
  btor_msg (btor,
            1,
            "gaussian elimination in linear equations: %d",
            btor->stats.gaussian_eliminations);
  btor_msg (btor,
            1,
            "eliminated sliced variables: %d",
            btor->stats.eliminated_slices);
  btor_msg (btor,
            1,
            "extracted skeleton constraints: %d",
            btor->stats.skeleton_constraints);
  btor_msg (btor, 1, "and normalizations: %d", btor->stats.ands_normalized);
  btor_msg (btor, 1, "add normalizations: %d", btor->stats.adds_normalized);
  btor_msg (btor, 1, "mul normalizations: %d", btor->stats.muls_normalized);
  btor_msg (btor,
            1,
            "synthesis assignment inconsistencies: %d",
            btor->stats.synthesis_assignment_inconsistencies);
  btor_msg (
      btor, 1, "  apply nodes: %d", btor->stats.synthesis_inconsistency_apply);
  btor_msg (btor,
            1,
            "  lambda nodes: %d",
            btor->stats.synthesis_inconsistency_lambda);
  btor_msg (
      btor, 1, "  var nodes: %d", btor->stats.synthesis_inconsistency_var);

  btor_msg (btor,
            1,
            "apply propagation during construction: %d",
            btor->stats.apply_props_construct);
  btor_msg (btor, 1, "beta reductions: %lld", btor->stats.beta_reduce_calls);
  btor_msg (
      btor, 1, "expression evaluations: %lld", btor->stats.eval_exp_calls);
  btor_msg (btor,
            1,
            "synthesized lambda applies: %lld",
            btor->stats.lambda_synth_apps);
  btor_msg (
      btor, 1, "lambda chains merged: %lld", btor->stats.lambda_chains_merged);
  btor_msg (btor, 1, "lambdas merged: %lld", btor->stats.lambdas_merged);
  btor_msg (btor, 1, "propagations: %lld", btor->stats.propagations);
  btor_msg (btor, 1, "propagations down: %lld", btor->stats.propagations_down);

  btor_msg (btor, 1, "");
  btor_msg (btor, 1, "%.2f seconds beta-reduction", btor->time.beta);
  btor_msg (btor, 1, "%.2f seconds expression evaluation", btor->time.eval);
  btor_msg (btor, 1, "%.2f seconds lazy apply encoding", btor->time.enc_app);
  btor_msg (
      btor, 1, "%.2f seconds lazy lambda encoding", btor->time.enc_lambda);
  btor_msg (btor, 1, "%.2f seconds lazy var encoding", btor->time.enc_var);
  btor_msg (btor, 1, "%.2f seconds node search", btor->time.find_dfs);
  btor_msg (btor, 1, "");
  btor_msg (btor, 1, "%.2f seconds in rewriting engine", btor->time.rewrite);
  btor_msg (btor, 1, "%.2f seconds in pure SAT solving", btor->time.sat);
  btor_msg (btor, 1, "");
  btor_msg (btor,
            1,
            "%.2f seconds in variable substitution during rewriting (%.0f%%)",
            btor->time.subst,
            percent (btor->time.subst, btor->time.rewrite));
  btor_msg (
      btor,
      1,
      "%.2f seconds in embedded constraint replacing during rewriting (%.0f%%)",
      btor->time.embedded,
      percent (btor->time.embedded, btor->time.rewrite));
  btor_msg (btor,
            1,
            "%.2f seconds in beta reduction during rewriting (%.0f%%)",
            btor->time.betareduce,
            percent (btor->time.betareduce, btor->time.rewrite));
#ifndef BTOR_DO_NOT_ELIMINATE_SLICES
  btor_msg (btor,
            1,
            "%.2f seconds in slicing during rewriting (%.0f%%)",
            btor->time.slicing,
            percent (btor->time.slicing, btor->time.rewrite));
#endif
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  btor_msg (btor,
            1,
            "%.2f seconds skeleton preprocessing during rewriting (%.0f%%)",
            btor->time.skel,
            percent (btor->time.skel, btor->time.rewrite));
#endif
}

Btor *
btor_new_btor (void)
{
  BtorMemMgr *mm;
  Btor *btor;

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, btor);

  btor->mm = mm;

  btor->bv_assignments    = btor_new_bv_assignment_list (mm);
  btor->array_assignments = btor_new_array_assignment_list (mm);

  BTOR_INIT_UNIQUE_TABLE (mm, btor->nodes_unique_table);

  btor->avmgr = btor_new_aigvec_mgr (mm);

  btor->bv_vars = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
  btor->array_vars =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->lambdas = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);

  btor->bv_lambda_id      = 1;
  btor->array_lambda_id   = 1;
  btor->dvn_id            = 1;
  btor->dan_id            = 1;
  btor->valid_assignments = 1;
  btor->rewrite_level     = 3;
  btor->vread_index_id    = 1;
  btor->msgtick           = -1;
  btor->pprint            = 1;

  BTOR_PUSH_STACK (btor->mm, btor->nodes_id_table, 0);

  btor->lod_cache =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
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

  BTOR_INIT_STACK (btor->arrays_with_model);

  btor->true_exp = btor_true_exp (btor);

  return btor;
}

void
btor_delete_btor (Btor *btor)
{
  assert (btor);

  int i;
  BtorNodePtrStack stack;
  BtorPtrHashTable *t;
  BtorPtrHashBucket *b, *b_app;
  BtorMemMgr *mm;
  BtorNode *exp;

  mm = btor->mm;

  btor_release_exp (btor, btor->true_exp);

  btor_delete_bv_assignment_list (btor->bv_assignments);
  btor_delete_array_assignment_list (btor->array_assignments);

  for (b = btor->lod_cache->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->lod_cache);

  for (b = btor->varsubst_constraints->first; b; b = b->next)
  {
    btor_release_exp (btor, (BtorNode *) b->key);
    btor_release_exp (btor, (BtorNode *) b->data.asPtr);
  }
  btor_delete_ptr_hash_table (btor->varsubst_constraints);

  for (b = btor->embedded_constraints->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->embedded_constraints);

  for (b = btor->unsynthesized_constraints->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->unsynthesized_constraints);

  for (b = btor->synthesized_constraints->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->synthesized_constraints);

  for (b = btor->assumptions->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->assumptions);

  if (btor->model_gen)
  {
    for (b = btor->var_rhs->first; b; b = b->next)
      btor_release_exp (btor, (BtorNode *) b->key);
    btor_delete_ptr_hash_table (btor->var_rhs);

    for (b = btor->array_rhs->first; b; b = b->next)
      btor_release_exp (btor, (BtorNode *) b->key);
    btor_delete_ptr_hash_table (btor->array_rhs);
  }

  for (i = 0; i < BTOR_COUNT_STACK (btor->arrays_with_model); i++)
    btor_release_exp (btor, btor->arrays_with_model.start[i]);
  BTOR_RELEASE_STACK (mm, btor->arrays_with_model);

  BTOR_INIT_STACK (stack);
  for (b = btor->lambdas->first; b; b = b->next)
  {
    t = ((BtorLambdaNode *) b->key)->synth_apps;
    if (t)
    {
      for (b_app = t->first; b_app; b_app = b_app->next)
        BTOR_PUSH_STACK (mm, stack, (BtorNode *) b_app->key);
      ((BtorLambdaNode *) b->key)->synth_apps = 0;
      btor_delete_ptr_hash_table (t);
    }
  }

  while (!BTOR_EMPTY_STACK (stack))
    btor_release_exp (btor, BTOR_POP_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);

  if (btor->external_refs)
  {
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
    assert (btor->external_refs == 0);
    for (i = BTOR_COUNT_STACK (btor->nodes_id_table) - 1; i >= 0; i--)
      assert (!BTOR_PEEK_STACK (btor->nodes_id_table, i));
  }

#ifndef NDEBUG
  int k;
  BtorNode *cur;
  if (btor->nodes_unique_table.num_elements)
    BTORLOG ("*** btor->nodes_unique_table.num_elements: %d",
             0,
             btor->nodes_unique_table.num_elements);
  for (k = 0; k < btor->nodes_unique_table.size; k++)
    for (cur = btor->nodes_unique_table.chains[k]; cur; cur = cur->next)
      BTORLOG ("  unreleased node: %s (%d)", node2string (cur), cur->refs);
#endif
  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKEXP")
          || btor->nodes_unique_table.num_elements == 0);
  BTOR_RELEASE_UNIQUE_TABLE (mm, btor->nodes_unique_table);
  BTOR_RELEASE_STACK (mm, btor->nodes_id_table);

  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKSORT")
          || btor->sorts_unique_table.num_elements == 0);
  BTOR_RELEASE_UNIQUE_TABLE (mm, btor->sorts_unique_table);

  btor_delete_ptr_hash_table (btor->bv_vars);
  btor_delete_ptr_hash_table (btor->array_vars);
  btor_delete_ptr_hash_table (btor->lambdas);
  btor_delete_ptr_hash_table (btor->parameterized);

  btor_delete_aigvec_mgr (btor->avmgr);

  assert (btor->rec_rw_calls == 0);
  BTOR_DELETE (mm, btor);
  btor_delete_mem_mgr (mm);
}

/* synthesizes unsynthesized constraints and updates constraints tables.
 * returns 0 if a constraint has been synthesized into AIG_FALSE */
static int
process_unsynthesized_constraints (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *uc, *sc;
  BtorPtrHashBucket *bucket;
  BtorNode *cur;
  BtorAIG *aig;
  BtorAIGMgr *amgr;

  uc   = btor->unsynthesized_constraints;
  sc   = btor->synthesized_constraints;
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);

  while (uc->count > 0)
  {
    bucket = uc->first;
    assert (bucket);
    cur = (BtorNode *) bucket->key;

#ifndef NDEBUG
    if (btor->rewrite_level > 2)
    {
      BtorNode *real_cur = BTOR_REAL_ADDR_NODE (cur);
      if (real_cur->kind == BTOR_BEQ_NODE)
      {
        BtorNode *left  = real_cur->e[0];
        BtorNode *right = real_cur->e[1];
        BtorNode *other;

        if (BTOR_REAL_ADDR_NODE (left)->kind == BTOR_BV_CONST_NODE)
          other = right;
        else if (BTOR_REAL_ADDR_NODE (right)->kind == BTOR_BV_CONST_NODE)
          other = left;
        else
          other = 0;

        if (other && !BTOR_IS_INVERTED_NODE (other)
            && other->kind == BTOR_ADD_NODE)
        {
          assert (BTOR_REAL_ADDR_NODE (other->e[0])->kind
                  != BTOR_BV_CONST_NODE);
          assert (BTOR_REAL_ADDR_NODE (other->e[1])->kind
                  != BTOR_BV_CONST_NODE);
        }
      }
    }
#endif

    if (!btor_find_in_ptr_hash_table (sc, cur))
    {
      aig = btor_exp_to_aig (btor, cur);
      if (aig == BTOR_AIG_FALSE) return 1;

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
  return 0;
}

static void
update_assumptions (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *ass;
  BtorPtrHashBucket *b;
  BtorNode *cur, *simp;

  ass = btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

  for (b = btor->assumptions->first; b; b = b->next)
  {
    cur = (BtorNode *) b->key;
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

  BtorPtrHashTable *uc;
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

  BtorPtrHashTable *embedded_constraints;
  embedded_constraints = btor->embedded_constraints;
  if (!btor_find_in_ptr_hash_table (embedded_constraints, exp))
  {
    assert (
        !btor_find_in_ptr_hash_table (btor->unsynthesized_constraints, exp));
    (void) btor_insert_in_ptr_hash_table (embedded_constraints,
                                          btor_copy_exp (btor, exp));
    BTOR_REAL_ADDR_NODE (exp)->constraint = 1;
    btor->stats.constraints.embedded++;
  }
}

static void
insert_varsubst_constraint (Btor *btor, BtorNode *left, BtorNode *right)
{
  BtorNode *eq;
  BtorPtrHashTable *vsc;
  BtorPtrHashBucket *bucket;

  assert (btor);
  assert (left);
  assert (right);

  vsc    = btor->varsubst_constraints;
  bucket = btor_find_in_ptr_hash_table (vsc, left);

  if (!bucket)
  {
    if (btor->model_gen && !BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (right))
        && !btor_find_in_ptr_hash_table (btor->var_rhs, left))
    {
      btor_insert_in_ptr_hash_table (btor->var_rhs, btor_copy_exp (btor, left));
    }

    if (btor->model_gen && BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (right))
        && !btor_find_in_ptr_hash_table (btor->array_rhs, left))
    {
      btor_insert_in_ptr_hash_table (btor->array_rhs,
                                     btor_copy_exp (btor, left));
    }

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

static BtorNode *
lambda_var_exp (Btor *btor, int len)
{
  BtorNode *result;
  char *name;
  int string_len;
  BtorMemMgr *mm;

  assert (btor);
  assert (len > 0);

  mm = btor->mm;

  string_len = btor_num_digits_util (btor->bv_lambda_id) + 11;
  BTOR_NEWN (mm, name, string_len);
  sprintf (name, "bvlambda_%d_", btor->bv_lambda_id);
  btor->bv_lambda_id++;
  result = btor_var_exp (btor, len, name);
  BTOR_DELETEN (mm, name, string_len);
  return result;
}

/* check if left does not occur on the right side */
static int
occurrence_check (Btor *btor, BtorNode *left, BtorNode *right)
{
  BtorNode *cur, *real_left;
  BtorNodePtrStack stack, unmark_stack;
  int is_cyclic, i;
  BtorMemMgr *mm;
  assert (btor);
  assert (left);
  assert (right);

  is_cyclic = 0;
  mm        = btor->mm;
  real_left = BTOR_REAL_ADDR_NODE (left);
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  cur = BTOR_REAL_ADDR_NODE (right);
  goto OCCURRENCE_CHECK_ENTER_WITHOUT_POP;

  do
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
  OCCURRENCE_CHECK_ENTER_WITHOUT_POP:
    assert (cur->aux_mark == 0 || cur->aux_mark == 1);
    if (cur->aux_mark == 0)
    {
      cur->aux_mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, cur);
      if (cur == real_left)
      {
        is_cyclic = 1;
        break;
      }
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->aux_mark == 1);
    cur->aux_mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);

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
  char *ic, *fc, *bits;
  BtorMemMgr *mm;
  BtorSubstCompKind comp;

  assert (btor);
  assert (exp);
  assert (left_result);
  assert (right_result);
  assert (btor->rewrite_level > 1);
  assert (btor_simplify_exp (btor, exp) == exp);

  mm = btor->mm;

  /* boolean BV_NODE, force assignment (right_result) w.r.t. phase */
  if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (exp)))
  {
    assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
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
      bits = btor_not_const_3vl (mm, BTOR_REAL_ADDR_NODE (right)->bits);
    else
      bits = btor_copy_const (mm, right->bits);

    if (comp == BTOR_SUBST_COMP_ULT_KIND || comp == BTOR_SUBST_COMP_ULTE_KIND)
    {
      leadings = btor_get_num_leading_zeros_const (btor->mm, bits);
      if (leadings > 0)
      {
        const_exp = btor_zero_exp (btor, leadings);
        lambda    = lambda_var_exp (btor, var->len - leadings);
        tmp       = btor_concat_exp (btor, const_exp, lambda);
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
      leadings = btor_get_num_leading_ones_const (btor->mm, bits);
      if (leadings > 0)
      {
        const_exp = btor_ones_exp (btor, leadings);
        lambda    = lambda_var_exp (btor, var->len - leadings);
        tmp       = btor_concat_exp (btor, const_exp, lambda);
        insert_varsubst_constraint (btor, var, tmp);
        btor_release_exp (btor, const_exp);
        btor_release_exp (btor, lambda);
        btor_release_exp (btor, tmp);
      }
    }

    btor_delete_const (btor->mm, bits);
    return 0;
  }

  /* in the boolean case a != b is the same as a == ~b */
  if (BTOR_IS_INVERTED_NODE (exp)
      && BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_BEQ_NODE
      && BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (exp)->e[0])->len == 1)
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
      && !BTOR_IS_ARRAY_VAR_NODE (real_left)
      && !BTOR_IS_ARRAY_VAR_NODE (real_right))
  {
    if (btor_rewrite_linear_term (btor, left, &fc, left_result, &tmp))
      *right_result = btor_sub_exp (btor, right, tmp);
    else if (btor_rewrite_linear_term (btor, right, &fc, left_result, &tmp))
      *right_result = btor_sub_exp (btor, left, tmp);
    else
      return 0;

    btor->stats.gaussian_eliminations++;

    btor_release_exp (btor, tmp);
    ic = btor_inverse_const (btor->mm, fc);
    btor_delete_const (btor->mm, fc);
    inv = btor_const_exp (btor, ic);
    btor_delete_const (btor->mm, ic);
    tmp = btor_mul_exp (btor, *right_result, inv);
    btor_release_exp (btor, inv);
    btor_release_exp (btor, *right_result);
    *right_result = tmp;
  }
  else
  {
    if ((!BTOR_IS_BV_VAR_NODE (real_left) && BTOR_IS_BV_VAR_NODE (real_right))
        || (!BTOR_IS_ARRAY_VAR_NODE (real_left)
            && BTOR_IS_ARRAY_VAR_NODE (real_right)))
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
  assert (btor->rewrite_level > 1);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  BtorNode *rep;

  rep = btor_simplify_exp (btor, exp);

  return rep == BTOR_INVERT_NODE (rep);
}

static int
has_parents_exp (Btor *btor, BtorNode *exp)
{
  BtorFullParentIterator it;

  assert (btor);
  assert (exp);
  (void) btor;

  init_full_parent_iterator (&it, exp);
  return has_next_parent_full_parent_iterator (&it);
}

static int
is_embedded_constraint_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->len == 1 && has_parents_exp (btor, exp);
}

static void
insert_new_constraint (Btor *btor, BtorNode *exp)
{
  BtorNode *left, *right, *real_exp;
  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  if (btor->inconsistent) return;

  exp      = btor_simplify_exp (btor, exp);
  real_exp = BTOR_REAL_ADDR_NODE (exp);

  if (BTOR_IS_BV_CONST_NODE (real_exp))
  {
    if ((BTOR_IS_INVERTED_NODE (exp) && real_exp->bits[0] == '1')
        || (!BTOR_IS_INVERTED_NODE (exp) && real_exp->bits[0] == '0'))
    {
      btor->inconsistent = 1;
      return;
    }
    else
    {
      /* we do not add true */
      assert ((BTOR_IS_INVERTED_NODE (exp) && real_exp->bits[0] == '0')
              || (!BTOR_IS_INVERTED_NODE (exp) && real_exp->bits[0] == '1'));
      return;
    }
  }

  if (!btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp))
  {
    if (btor->rewrite_level > 1)
    {
      if (normalize_substitution (btor, exp, &left, &right))
      {
        insert_varsubst_constraint (btor, left, right);
        btor_release_exp (btor, left);
        btor_release_exp (btor, right);
      }
      else
      {
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
            assert (btor_find_in_ptr_hash_table (
                        btor->unsynthesized_constraints, exp)
                    || btor_find_in_ptr_hash_table (btor->embedded_constraints,
                                                    exp));
          }
        }
      }
    }
    else
      insert_unsynthesized_constraint (btor, exp);

    report_constraint_stats (btor, 0);
  }
}

static void
btor_reset_assumptions (Btor *btor)
{
  BtorPtrHashBucket *bucket;
  assert (btor);
  for (bucket = btor->assumptions->first; bucket; bucket = bucket->next)
    btor_release_exp (btor, (BtorNode *) bucket->key);
  btor_delete_ptr_hash_table (btor->assumptions);
  btor->assumptions =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
btor_reset_array_models (Btor *btor)
{
  BtorNode *cur;
  int i;

  assert (btor);

  for (i = 0; i < BTOR_COUNT_STACK (btor->arrays_with_model); i++)
  {
    cur = btor->arrays_with_model.start[i];
    assert (!BTOR_IS_INVERTED_NODE (cur));
    assert (BTOR_IS_ARRAY_NODE (cur));
    assert (cur->rho);
    btor_delete_ptr_hash_table (cur->rho);
    cur->rho = 0;
    btor_release_exp (btor, cur);
  }
  BTOR_RESET_STACK (btor->arrays_with_model);
}

static void
btor_reset_incremental_usage (Btor *btor)
{
  assert (btor);

  btor_reset_assumptions (btor);
  btor_reset_array_models (btor);
  btor->valid_assignments = 0;
}

static void
add_constraint (Btor *btor, BtorNode *exp)
{
  BtorNode *cur, *child;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;

  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  mm = btor->mm;
  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!BTOR_IS_INVERTED_NODE (exp) && exp->kind == BTOR_AND_NODE)
  {
    BTOR_INIT_STACK (stack);
    cur = exp;
    goto ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP:
      assert (!BTOR_IS_INVERTED_NODE (cur));
      assert (cur->kind == BTOR_AND_NODE);
      assert (cur->mark == 0 || cur->mark == 1);
      if (!cur->mark)
      {
        cur->mark = 1;
        child     = cur->e[1];
        if (!BTOR_IS_INVERTED_NODE (child) && child->kind == BTOR_AND_NODE)
          BTOR_PUSH_STACK (mm, stack, child);
        else
          insert_new_constraint (btor, child);
        child = cur->e[0];
        if (!BTOR_IS_INVERTED_NODE (child) && child->kind == BTOR_AND_NODE)
          BTOR_PUSH_STACK (mm, stack, child);
        else
          insert_new_constraint (btor, child);
      }
    } while (!BTOR_EMPTY_STACK (stack));
    BTOR_RELEASE_STACK (mm, stack);
    btor_mark_exp (btor, exp, 0);
  }
  else
    insert_new_constraint (btor, exp);
}

void
btor_assert_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  add_constraint (btor, exp);
}

void
btor_assume_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *cur, *child;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;

  assert (btor);
  assert (btor->inc_enabled);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  mm = btor->mm;
  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!BTOR_IS_INVERTED_NODE (exp) && exp->kind == BTOR_AND_NODE)
  {
    BTOR_INIT_STACK (stack);
    cur = exp;
    goto BTOR_ADD_ASSUMPTION_NODE_ENTER_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    BTOR_ADD_ASSUMPTION_NODE_ENTER_WITHOUT_POP:
      assert (!BTOR_IS_INVERTED_NODE (cur));
      assert (cur->kind == BTOR_AND_NODE);
      assert (cur->mark == 0 || cur->mark == 1);
      if (!cur->mark)
      {
        cur->mark = 1;
        child     = cur->e[1];
        if (!BTOR_IS_INVERTED_NODE (child) && child->kind == BTOR_AND_NODE)
        {
          BTOR_PUSH_STACK (mm, stack, child);
        }
        else
        {
          if (!btor_find_in_ptr_hash_table (btor->assumptions, child))
            (void) btor_insert_in_ptr_hash_table (btor->assumptions,
                                                  btor_copy_exp (btor, child));
        }
        child = cur->e[0];
        if (!BTOR_IS_INVERTED_NODE (child) && child->kind == BTOR_AND_NODE)
        {
          BTOR_PUSH_STACK (mm, stack, child);
        }
        else
        {
          if (!btor_find_in_ptr_hash_table (btor->assumptions, child))
            (void) btor_insert_in_ptr_hash_table (btor->assumptions,
                                                  btor_copy_exp (btor, child));
        }
      }
    } while (!BTOR_EMPTY_STACK (stack));
    BTOR_RELEASE_STACK (mm, stack);
    btor_mark_exp (btor, exp, 0);
  }
  else
  {
    if (!btor_find_in_ptr_hash_table (btor->assumptions, exp))
      (void) btor_insert_in_ptr_hash_table (btor->assumptions,
                                            btor_copy_exp (btor, exp));
  }
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
  assert (exp->len == BTOR_REAL_ADDR_NODE (simplified)->len);
  assert (btor->rewrite_level > 1 || btor->beta_reduce_all);

  if (exp->simplified) btor_release_exp (btor, exp->simplified);

  exp->simplified = btor_copy_exp (btor, simplified);

  if (exp->constraint) update_constraints (btor, exp);

  btor_set_to_proxy_exp (btor, exp);

#if 0
  if (exp->kind == BTOR_AEQ_NODE && exp->vreads)
    {
      btor_release_exp (btor, exp->vreads->exp2);
      btor_release_exp (btor, exp->vreads->exp1);
      BTOR_DELETE (btor->mm, exp->vreads);
      exp->vreads = 0;
    }

  remove_from_nodes_unique_table_exp (btor, exp);
  /* also updates op stats */
  erase_local_data_exp (btor, exp, 0);
  btor->ops[BTOR_PROXY_NODE]++;
  assert (exp->arity <= 3);
  memset (e, 0, sizeof e);
  for (i = 0; i < exp->arity; i++)
    e[i] = exp->e[i];
  remove_from_hash_tables (btor, exp);
  disconnect_children_exp (btor, exp);
  for (i = 0; i < exp->arity; i++)
    btor_release_exp (btor, e[i]);
  exp->kind = BTOR_PROXY_NODE;
  exp->disconnected = 0;
  exp->erased = 0;
  exp->arity = 0;
  exp->parameterized = 0;
#endif
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

BtorNode *
simplify_constraint_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->constraint);
  assert (!BTOR_REAL_ADDR_NODE (exp)->simplified);

  BtorNode *real_exp, *result, *not_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  not_exp  = BTOR_INVERT_NODE (real_exp);

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

  BtorNode *real_exp, *result;
  BtorPtrHashBucket *bucket;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  // TODO: should we move that to the bottom?
  if (real_exp->constraint) return simplify_constraint_exp (btor, exp);

  // TODO: substitution flag for BtorNode?
  if (btor->substitutions)
  {
    BtorNode *simp;
    simp = btor_pointer_chase_simplified_exp (btor, real_exp);

    bucket = btor_find_in_ptr_hash_table (btor->substitutions,
                                          BTOR_REAL_ADDR_NODE (simp));
    if (bucket)
      result = btor_pointer_chase_simplified_exp (btor, bucket->data.asPtr);
    else
      result = simp;

    if (BTOR_IS_INVERTED_NODE (exp)) return BTOR_INVERT_NODE (result);
    return result;
  }

  result = btor_pointer_chase_simplified_exp (btor, exp);

  if (BTOR_REAL_ADDR_NODE (result)->constraint)
    return simplify_constraint_exp (btor, result);

  return result;
}

/*------------------------------------------------------------------------*/

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
    case BTOR_ARRAY_VAR_NODE:
    case BTOR_PARAM_NODE:
      return btor_copy_exp (btor,
                            btor_pointer_chase_simplified_exp (btor, exp));
    case BTOR_SLICE_NODE:
      return btor_slice_exp (btor, exp->e[0], exp->upper, exp->lower);
    case BTOR_AND_NODE: return btor_and_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_BEQ_NODE:
    case BTOR_AEQ_NODE: return btor_eq_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ADD_NODE: return btor_add_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_MUL_NODE: return btor_mul_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ULT_NODE: return btor_ult_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SLL_NODE: return btor_sll_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SRL_NODE: return btor_srl_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UDIV_NODE: return btor_udiv_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UREM_NODE: return btor_urem_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_CONCAT_NODE: return btor_concat_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_LAMBDA_NODE:
      assert (!btor_param_cur_assignment (exp->e[0]));
      BTOR_PARAM_SET_LAMBDA_NODE (exp->e[0], 0);
      return btor_lambda_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_APPLY_NODE: return btor_apply_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ARGS_NODE: return btor_args_exp (btor, exp->arity, exp->e);
    default:
      assert (BTOR_IS_BV_COND_NODE (exp));
      return btor_cond_exp (btor, exp->e[0], exp->e[1], exp->e[2]);
  }
}

/* we perform all variable substitutions in one pass and rebuild the formula
 * cyclic substitutions must have been deleted before! */
static void
substitute_vars_and_rebuild_exps (Btor *btor, BtorPtrHashTable *substs)
{
  BtorNodePtrStack stack, root_stack;
  BtorPtrHashBucket *b;
  BtorNode *cur, *cur_parent, *rebuilt_exp, **temp, **top, *rhs, *simplified;
  BtorMemMgr *mm;
  BtorFullParentIterator it;
  int pushed, i;
  assert (btor);
  assert (substs);

  if (substs->count == 0u) return;

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (root_stack);
  /* search upwards for all reachable roots */
  /* we push all left sides on the search stack */
  for (b = substs->first; b; b = b->next)
  {
    cur = (BtorNode *) b->key;
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
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
      init_full_parent_iterator (&it, cur);
      /* are we at a root ? */
      pushed = 0;
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
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
      if (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur))
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
      if (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur))
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
          btor->stats.array_substitutions++;
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
}

static void
substitute_var_exps (Btor *btor)
{
  BtorPtrHashTable *varsubst_constraints, *order, *substs;
  BtorNode *cur, *constraint, *left, *right, *child;
  BtorPtrHashBucket *b, *b_temp;
  int order_num, val, max, i;
  BtorNodePtrStack stack;
  double start, delta;
  unsigned count;
  BtorMemMgr *mm;

  assert (btor);
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
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
      btor_insert_in_ptr_hash_table (substs, cur)->data.asPtr = b->data.asPtr;
      btor_remove_from_ptr_hash_table (varsubst_constraints, cur, 0, 0);
    }
    assert (varsubst_constraints->count == 0u);

    /* we search for cyclic substitution dependencies
     * and map the substitutions to an ordering number */
    for (b = substs->first; b; b = b->next)
    {
      cur = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
      BTOR_PUSH_STACK (mm, stack, (BtorNode *) cur);

      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

        if (!cur)
        {
          cur = BTOR_POP_STACK (stack); /* left */
          assert (BTOR_IS_REGULAR_NODE (cur));
          assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
          assert (!btor_find_in_ptr_hash_table (order, cur));
          btor_insert_in_ptr_hash_table (order, cur)->data.asInt = order_num++;
          continue;
        }

        if (cur->mark == 1) /* visited (DFS) */
          continue;

        cur->mark = 1;

        if (BTOR_IS_BV_CONST_NODE (cur) || BTOR_IS_BV_VAR_NODE (cur)
            || BTOR_IS_ARRAY_VAR_NODE (cur) || BTOR_IS_PARAM_NODE (cur))
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
    for (b = substs->first; b; b = b->next)
    {
      assert (BTOR_IS_REGULAR_NODE ((BtorNode *) b->key));
      assert (BTOR_IS_BV_VAR_NODE ((BtorNode *) b->key)
              || BTOR_IS_ARRAY_VAR_NODE ((BtorNode *) b->key));
      btor_mark_exp (btor, (BtorNode *) b->key, 0);
      btor_mark_exp (btor, (BtorNode *) b->data.asPtr, 0);
    }

    /* we look for cycles */
    for (b = substs->first; b; b = b->next)
    {
#ifndef NDEBUG
      cur = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
#endif
      BTOR_PUSH_STACK (mm, stack, (BtorNode *) b->data.asPtr);

      /* we assume that there are no direct loops
       * as a result of occurrence check */
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

        if (cur->mark == 2) /* cur has max order of its children */
          continue;

        if (BTOR_IS_BV_CONST_NODE (cur) || BTOR_IS_BV_VAR_NODE (cur)
            || BTOR_IS_ARRAY_VAR_NODE (cur) || BTOR_IS_PARAM_NODE (cur))
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
    for (b = substs->first; b; b = b->next)
    {
      left = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (BTOR_IS_BV_VAR_NODE (left) || BTOR_IS_ARRAY_VAR_NODE (left));
      right = (BtorNode *) b->data.asPtr;
      btor_mark_exp (btor, left, 0);
      btor_mark_exp (btor, right, 0);
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
      assert (BTOR_IS_BV_VAR_NODE (left) || BTOR_IS_ARRAY_VAR_NODE (left));
      right =
          (BtorNode *) btor_find_in_ptr_hash_table (substs, left)->data.asPtr;
      assert (right);

      constraint = btor_eq_exp (btor, left, right);
      insert_unsynthesized_constraint (btor, constraint);
      btor_release_exp (btor, constraint);

      btor_remove_from_ptr_hash_table (substs, left, 0, 0);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    /* we rebuild and substiute variables in one pass */
    substitute_vars_and_rebuild_exps (btor, substs);

    /* cleanup, we delete all substitution constraints */
    for (b = substs->first; b; b = b->next)
    {
      left = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (left->kind == BTOR_PROXY_NODE);
      assert (left->simplified);
      right = (BtorNode *) b->data.asPtr;
      assert (right);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    btor_delete_ptr_hash_table (order);
    btor_delete_ptr_hash_table (substs);
  }

  BTOR_RELEASE_STACK (mm, stack);
  delta = btor_time_stamp () - start;
  btor->time.subst += delta;
  btor_msg (btor, 1, "%d variables substituted in %.1f seconds", count, delta);
}

static int
all_exps_below_rebuilt (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int i;
  BtorNode *subst;

  if (btor->substitutions)
  {
    subst = btor_find_substitution (btor, exp);
    if (subst && BTOR_REAL_ADDR_NODE (subst)->aux_mark != 0) return 0;
  }

  exp = BTOR_REAL_ADDR_NODE (exp);
  for (i = 0; i < exp->arity; i++)
    if (BTOR_REAL_ADDR_NODE (exp->e[i])->aux_mark > 0) return 0;

  return 1;
}

static void
substitute_and_rebuild (Btor *btor, BtorPtrHashTable *subst, int bra)
{
  assert (btor);
  assert (subst);
  assert (bra == 0 || bra == 1);

  int i, pushed;
  BtorMemMgr *mm;
  BtorNode *cur, *cur_parent, *rebuilt_exp, *simplified;
  BtorNodePtrStack roots;
  BtorNodePtrQueue queue;
  BtorPtrHashBucket *b;
  BtorFullParentIterator it;

  if (subst->count == 0u) return;

  mm = btor->mm;

  BTOR_INIT_STACK (roots);
  BTOR_INIT_QUEUE (queue);

  assert (check_unique_table_mark_unset_dbg (btor));
  assert (check_unique_table_aux_mark_unset_dbg (btor));
  for (b = subst->first; b; b = b->next)
  {
    cur = BTOR_REAL_ADDR_NODE ((BtorNode *) b->key);
    assert (!BTOR_IS_PROXY_NODE (cur));
    if (bra) cur->mark = 1; /* mark as in substitute table */
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

      pushed = 0;
      init_full_parent_iterator (&it, cur);
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        BTOR_ENQUEUE (mm, queue, cur_parent);
        pushed = 1;
      }
      if (!pushed) BTOR_PUSH_STACK (mm, roots, btor_copy_exp (btor, cur));
    }
  }

  for (b = subst->first; b; b = b->next)
  {
    cur = BTOR_REAL_ADDR_NODE ((BtorNode *) b->key);
    assert (cur->aux_mark == 1);
    if (all_exps_below_rebuilt (btor, cur))
    {
      BTOR_ENQUEUE (mm, queue, cur);
      cur->aux_mark = 2; /* mark as enqueued */
    }
  }

  /* rebuild bottom-up */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!BTOR_IS_PROXY_NODE (cur));
    assert (cur->aux_mark == 2);
    cur->aux_mark = 1;

    if (all_exps_below_rebuilt (btor, cur))
    {
      cur->aux_mark = 0;

      init_full_parent_iterator (&it, cur);
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        /* cur might get a new parent while rebuilding due to
         * simplification */
        if (cur_parent->aux_mark == 0 || cur_parent->aux_mark == 1)
        {
          BTOR_ENQUEUE (mm, queue, cur_parent);
          cur_parent->aux_mark = 2;
        }
      }

      simplified = btor_find_substitution (btor, cur);

      if (simplified)
      {
        assert (BTOR_REAL_ADDR_NODE (simplified) != cur);
        assert (!BTOR_REAL_ADDR_NODE (simplified)->simplified);
        set_simplified_exp (btor, cur, simplified);
        continue;
      }

      if (bra && BTOR_IS_APPLY_NODE (cur) && cur->mark)
      {
        cur->mark   = 0;
        rebuilt_exp = btor_beta_reduce_full (btor, cur);
      }
      else
      {
        assert (!cur->mark);
        rebuilt_exp = rebuild_exp (btor, cur);
      }

      assert (rebuilt_exp);
      /* base case: rebuilt_exp == cur */
      if (rebuilt_exp != cur)
      {
        simplified = btor_simplify_exp (btor, rebuilt_exp);
        set_simplified_exp (btor, cur, simplified);
      }

      btor_release_exp (btor, rebuilt_exp);
    }
    /* not all children rebuilt, enqueue again */
    else
    {
      cur->aux_mark = 2;
      BTOR_ENQUEUE (mm, queue, cur);
    }
  }

  BTOR_RELEASE_QUEUE (mm, queue);

  for (i = 0; i < BTOR_COUNT_STACK (roots); i++)
    btor_release_exp (btor, roots.start[i]);

  BTOR_RELEASE_STACK (mm, roots);

  assert (check_unique_table_mark_unset_dbg (btor));
  assert (check_unique_table_aux_mark_unset_dbg (btor));
}

static void
substitute_embedded_constraints (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorNode *cur;

  assert (btor);

  for (b = btor->embedded_constraints->first; b; b = b->next)
  {
    cur = (BtorNode *) b->key;
    assert (BTOR_REAL_ADDR_NODE (cur)->constraint);
    /* embedded constraints have possibly lost their parents,
     * e.g. top conjunction of constraints that are released */
    if (has_parents_exp (btor, cur)) btor->stats.ec_substitutions++;
  }
  substitute_and_rebuild (btor, btor->embedded_constraints, 0);
}

static void
process_embedded_constraints (Btor *btor)
{
  BtorPtrHashTable *embedded_constraints;
  BtorPtrHashBucket *b;
  double start, delta;
  BtorNode *cur;
  int count;
  assert (btor);
  embedded_constraints = btor->embedded_constraints;
  if (embedded_constraints->count > 0u)
  {
    start = btor_time_stamp ();
    count = 0;
    substitute_embedded_constraints (btor);

    while (embedded_constraints->count > 0u)
    {
      count++;
      b   = embedded_constraints->first;
      cur = (BtorNode *) b->key;
      btor_remove_from_ptr_hash_table (embedded_constraints, cur, 0, 0);
      insert_unsynthesized_constraint (btor, cur);
      btor_release_exp (btor, cur);
    }
    delta = btor_time_stamp () - start;
    btor->time.embedded += delta;
    btor_msg (btor,
              1,
              "replaced %d embedded constraints in %1.f seconds",
              count,
              delta);
  }
}

/*------------------------------------------------------------------------*/
#ifndef BTOR_DO_NOT_ELIMINATE_SLICES
/*------------------------------------------------------------------------*/

struct BtorSlice
{
  int upper;
  int lower;
};

typedef struct BtorSlice BtorSlice;

static BtorSlice *
new_slice (Btor *btor, int upper, int lower)
{
  BtorSlice *result;

  assert (btor != NULL);
  assert (upper >= lower);
  assert (lower >= 0);

  BTOR_NEW (btor->mm, result);
  result->upper = upper;
  result->lower = lower;
  return result;
}

static void
delete_slice (Btor *btor, BtorSlice *slice)
{
  assert (btor != NULL);
  assert (slice != NULL);
  BTOR_DELETE (btor->mm, slice);
}

static unsigned int
hash_slice (BtorSlice *slice)
{
  unsigned int result;

  assert (slice != NULL);
  assert (slice->upper >= slice->lower);
  assert (slice->lower >= 0);

  result = (unsigned int) slice->upper;
  result += (unsigned int) slice->lower;
  result *= 7334147u;
  return result;
}

static int
compare_slices (BtorSlice *s1, BtorSlice *s2)
{
  assert (s1 != NULL);
  assert (s2 != NULL);
  assert (s1->upper >= s1->lower);
  assert (s1->lower >= 0);
  assert (s2->upper >= s2->lower);
  assert (s2->lower >= 0);

  if (s1->upper < s2->upper) return -1;

  if (s1->upper > s2->upper) return 1;

  assert (s1->upper == s1->upper);
  if (s1->lower < s2->lower) return -1;

  if (s1->lower > s2->lower) return 1;

  assert (s1->upper == s2->upper && s1->lower == s2->lower);
  return 0;
}

static int
compare_slices_qsort (const void *p1, const void *p2)
{
  return compare_slices (*((BtorSlice **) p1), *((BtorSlice **) p2));
}

static int
compare_int_ptr (const void *p1, const void *p2)
{
  int v1 = *((int *) p1);
  int v2 = *((int *) p2);
  if (v1 < v2) return -1;

  if (v1 > v2) return 1;

  return 0;
}

static void
eliminate_slices_on_bv_vars (Btor *btor)
{
  BtorNode *var, *cur, *result, *lambda_var, *temp;
  BtorSlice *s1, *s2, *new_s1, *new_s2, *new_s3, **sorted_slices;
  BtorPtrHashBucket *b_var, *b1, *b2;
  BtorFullParentIterator it;
  BtorPtrHashTable *slices;
  int i, min, max, count;
  BtorNodePtrStack vars;
  double start, delta;
  BtorMemMgr *mm;
  int vals[4];

  assert (btor != NULL);

  start = btor_time_stamp ();
  count = 0;

  mm = btor->mm;
  BTOR_INIT_STACK (vars);
  for (b_var = btor->bv_vars->first; b_var != NULL; b_var = b_var->next)
  {
    var = (BtorNode *) b_var->key;
    BTOR_PUSH_STACK (mm, vars, var);
  }

  while (!BTOR_EMPTY_STACK (vars))
  {
    slices = btor_new_ptr_hash_table (
        mm, (BtorHashPtr) hash_slice, (BtorCmpPtr) compare_slices);
    var = BTOR_POP_STACK (vars);
    assert (BTOR_IS_REGULAR_NODE (var));
    assert (BTOR_IS_BV_VAR_NODE (var));
    init_full_parent_iterator (&it, var);
    /* find all slices on variable */
    while (has_next_parent_full_parent_iterator (&it))
    {
      cur = next_parent_full_parent_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));
      if (cur->kind == BTOR_SLICE_NODE)
      {
        s1 = new_slice (btor, cur->upper, cur->lower);
        assert (!btor_find_in_ptr_hash_table (slices, s1));
        btor_insert_in_ptr_hash_table (slices, s1);
      }
    }

    /* no splitting necessary? */
    if (slices->count == 0u)
    {
      btor_delete_ptr_hash_table (slices);
      continue;
    }

    /* add full slice */
    s1 = new_slice (btor, var->len - 1, 0);
    assert (!btor_find_in_ptr_hash_table (slices, s1));
    btor_insert_in_ptr_hash_table (slices, s1);

  BTOR_SPLIT_SLICES_RESTART:
    for (b1 = slices->last; b1 != NULL; b1 = b1->prev)
    {
      s1 = (BtorSlice *) b1->key;
      for (b2 = b1->prev; b2 != NULL; b2 = b2->prev)
      {
        s2 = (BtorSlice *) b2->key;

        assert (compare_slices (s1, s2));

        /* not overlapping? */
        if ((s1->lower > s2->upper) || (s1->upper < s2->lower)
            || (s2->lower > s1->upper) || (s2->upper < s1->lower))
          continue;

        if (s1->upper == s2->upper)
        {
          assert (s1->lower != s2->lower);
          max    = BTOR_MAX_UTIL (s1->lower, s2->lower);
          min    = BTOR_MIN_UTIL (s1->lower, s2->lower);
          new_s1 = new_slice (btor, max - 1, min);
          if (!btor_find_in_ptr_hash_table (slices, new_s1))
            btor_insert_in_ptr_hash_table (slices, new_s1);
          else
            delete_slice (btor, new_s1);

          if (min == s1->lower)
          {
            btor_remove_from_ptr_hash_table (slices, s1, NULL, NULL);
            delete_slice (btor, s1);
          }
          else
          {
            btor_remove_from_ptr_hash_table (slices, s2, NULL, NULL);
            delete_slice (btor, s2);
          }
          goto BTOR_SPLIT_SLICES_RESTART;
        }

        if (s1->lower == s2->lower)
        {
          assert (s1->upper != s2->upper);
          max    = BTOR_MAX_UTIL (s1->upper, s2->upper);
          min    = BTOR_MIN_UTIL (s1->upper, s2->upper);
          new_s1 = new_slice (btor, max, min + 1);
          if (!btor_find_in_ptr_hash_table (slices, new_s1))
            btor_insert_in_ptr_hash_table (slices, new_s1);
          else
            delete_slice (btor, new_s1);
          if (max == s1->upper)
          {
            btor_remove_from_ptr_hash_table (slices, s1, NULL, NULL);
            delete_slice (btor, s1);
          }
          else
          {
            btor_remove_from_ptr_hash_table (slices, s2, NULL, NULL);
            delete_slice (btor, s2);
          }
          goto BTOR_SPLIT_SLICES_RESTART;
        }

        /* regular overlapping case (overlapping at both ends) */
        vals[0] = s1->upper;
        vals[1] = s1->lower;
        vals[2] = s2->upper;
        vals[3] = s2->lower;
        qsort (vals, 4, sizeof (int), compare_int_ptr);
        new_s1 = new_slice (btor, vals[3], vals[2] + 1);
        new_s2 = new_slice (btor, vals[2], vals[1]);
        new_s3 = new_slice (btor, vals[1] - 1, vals[0]);
        btor_remove_from_ptr_hash_table (slices, s1, NULL, NULL);
        btor_remove_from_ptr_hash_table (slices, s2, NULL, NULL);
        delete_slice (btor, s1);
        delete_slice (btor, s2);
        if (!btor_find_in_ptr_hash_table (slices, new_s1))
          btor_insert_in_ptr_hash_table (slices, new_s1);
        else
          delete_slice (btor, new_s1);
        if (!btor_find_in_ptr_hash_table (slices, new_s2))
          btor_insert_in_ptr_hash_table (slices, new_s2);
        else
          delete_slice (btor, new_s2);
        if (!btor_find_in_ptr_hash_table (slices, new_s3))
          btor_insert_in_ptr_hash_table (slices, new_s3);
        else
          delete_slice (btor, new_s3);
        goto BTOR_SPLIT_SLICES_RESTART;
      }
    }

    /* copy slices to sort them */
    assert (slices->count > 1u);
    BTOR_NEWN (mm, sorted_slices, slices->count);
    i = 0;
    for (b1 = slices->first; b1 != NULL; b1 = b1->next)
    {
      s1                 = (BtorSlice *) b1->key;
      sorted_slices[i++] = s1;
    }
    qsort (sorted_slices,
           slices->count,
           sizeof (BtorSlice *),
           compare_slices_qsort);

    s1     = sorted_slices[(int) slices->count - 1];
    result = lambda_var_exp (btor, s1->upper - s1->lower + 1);
    delete_slice (btor, s1);
    for (i = (int) slices->count - 2; i >= 0; i--)
    {
      s1         = sorted_slices[i];
      lambda_var = lambda_var_exp (btor, s1->upper - s1->lower + 1);
      temp       = btor_concat_exp (btor, result, lambda_var);
      btor_release_exp (btor, result);
      result = temp;
      btor_release_exp (btor, lambda_var);
      delete_slice (btor, s1);
    }
    BTOR_DELETEN (mm, sorted_slices, slices->count);
    btor_delete_ptr_hash_table (slices);

    count++;
    btor->stats.eliminated_slices++;
    insert_varsubst_constraint (btor, var, result);
    btor_release_exp (btor, result);
  }

  BTOR_RELEASE_STACK (mm, vars);

  delta = btor_time_stamp () - start;
  btor->time.slicing += delta;
  btor_msg (btor, 1, "sliced %d variables in %1.f seconds", count, delta);
}

/*------------------------------------------------------------------------*/
#endif /* BTOR_DO_NOT_ELIMINATE_SLICES */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
/*------------------------------------------------------------------------*/

#include "lglib.h"

static int
btor_fixed_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorAIG *aig;
  int res, id;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (real_exp->len == 1);
  if (!BTOR_IS_SYNTH_NODE (real_exp)) return 0;
  assert (real_exp->av);
  assert (real_exp->av->len == 1);
  assert (real_exp->av->aigs);
  aig = real_exp->av->aigs[0];
  if (aig == BTOR_AIG_TRUE)
    res = 1;
  else if (aig == BTOR_AIG_FALSE)
    res = -1;
  else
  {
    id = BTOR_GET_CNF_ID_AIG (aig);
    if (!id) return 0;
    amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
    smgr = btor_get_sat_mgr_aig_mgr (amgr);
    res  = btor_fixed_sat (smgr, id);
  }
  if (BTOR_IS_INVERTED_NODE (exp)) res = -res;
  return res;
}

static int
process_skeleton_tseitin_lit (BtorPtrHashTable *ids, BtorNode *exp)
{
  BtorPtrHashBucket *b;
  BtorNode *real_exp;
  int res;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (real_exp->len == 1);
  b = btor_find_in_ptr_hash_table (ids, real_exp);
  if (!b)
  {
    b             = btor_insert_in_ptr_hash_table (ids, real_exp);
    b->data.asInt = (int) ids->count;
  }

  res = b->data.asInt;
  assert (res > 0);

  if (BTOR_IS_INVERTED_NODE (exp)) res = -res;

  return res;
}

static void
process_skeleton_tseitin (Btor *btor,
                          LGL *lgl,
                          BtorNodePtrStack *work_stack,
                          BtorNodePtrStack *unmark_stack,
                          BtorPtrHashTable *ids,
                          BtorNode *root)
{
  int i, lhs, rhs[3], fixed;
  BtorNode *exp;

  BTOR_PUSH_STACK (btor->mm, *work_stack, root);

  do
  {
    exp = BTOR_POP_STACK (*work_stack);
    assert (exp);
    exp = BTOR_REAL_ADDR_NODE (exp);
    if (!exp->mark)
    {
      exp->mark = 1;
      BTOR_PUSH_STACK (btor->mm, *unmark_stack, exp);

      BTOR_PUSH_STACK (btor->mm, *work_stack, exp);
      for (i = exp->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (btor->mm, *work_stack, exp->e[i]);
    }
    else if (exp->mark == 1)
    {
      exp->mark = 2;
      if (exp->len != 1 || BTOR_IS_FUN_NODE (exp) || BTOR_IS_ARGS_NODE (exp)
          || exp->parameterized)
        continue;

#ifndef NDEBUG
      for (i = 0; i < exp->arity; i++)
      {
        BtorNode *child = exp->e[i];
        child           = BTOR_REAL_ADDR_NODE (child);
        assert (child->mark == 2);
        if (child->len == 1 && !BTOR_IS_FUN_NODE (child)
            && !BTOR_IS_ARGS_NODE (child) && !child->parameterized)
          assert (btor_find_in_ptr_hash_table (ids, child));
      }
#endif
      lhs   = process_skeleton_tseitin_lit (ids, exp);
      fixed = btor_fixed_exp (btor, exp);
      if (fixed)
      {
        lgladd (lgl, (fixed > 0) ? lhs : -lhs);
        lgladd (lgl, 0);
      }

      switch (exp->kind)
      {
        case BTOR_AND_NODE:
          rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, 0);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);
          break;

        case BTOR_BEQ_NODE:
          if (BTOR_REAL_ADDR_NODE (exp->e[0])->len != 1) break;
          assert (BTOR_REAL_ADDR_NODE (exp->e[1])->len == 1);
          rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);

          lgladd (lgl, -lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);

          break;

        case BTOR_BCOND_NODE:
          assert (BTOR_REAL_ADDR_NODE (exp->e[0])->len == 1);
          if (BTOR_REAL_ADDR_NODE (exp->e[1])->len != 1) break;
          assert (BTOR_REAL_ADDR_NODE (exp->e[2])->len == 1);
          rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);
          rhs[2] = process_skeleton_tseitin_lit (ids, exp->e[2]);

          lgladd (lgl, -lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, rhs[2]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, -rhs[2]);
          lgladd (lgl, 0);
          break;

        default: assert (exp->kind != BTOR_PROXY_NODE); break;
      }
    }
  } while (!BTOR_EMPTY_STACK (*work_stack));
}

static void
process_skeleton (Btor *btor)
{
  BtorPtrHashTable *ids, *table;
  BtorNodePtrStack unmark_stack;
  int constraints, count, fixed;
  BtorNodePtrStack work_stack;
  BtorMemMgr *mm = btor->mm;
  BtorPtrHashBucket *b;
  double start, delta;
  int res, lit, val;
  BtorNode *exp;
  LGL *lgl;

  start = btor_time_stamp ();

  ids = btor_new_ptr_hash_table (mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

  lgl = lglinit ();
  lglsetprefix (lgl, "[lglskel] ");

  if (btor->verbosity)
  {
    lglsetopt (lgl, "verbose", btor->verbosity - 1);
    lglbnr ("Lingeling", "[lglskel] ", stdout);
    fflush (stdout);
  }
  else
    lglsetopt (lgl, "verbose", -1);

  count = 0;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);

  for (constraints = 0; constraints <= 1; constraints++)
  {
    table = constraints ? btor->synthesized_constraints
                        : btor->unsynthesized_constraints;
    for (b = table->first; b; b = b->next)
    {
      count++;
      exp = b->key;
      assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
      process_skeleton_tseitin (
          btor, lgl, &work_stack, &unmark_stack, ids, exp);
      lgladd (lgl, process_skeleton_tseitin_lit (ids, exp));
      lgladd (lgl, 0);
    }
  }

  BTOR_RELEASE_STACK (mm, work_stack);

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    exp = BTOR_POP_STACK (unmark_stack);
    assert (!BTOR_IS_INVERTED_NODE (exp));
    assert (exp->mark);
    exp->mark = 0;
  }

  BTOR_RELEASE_STACK (mm, unmark_stack);

  btor_msg (btor,
            1,
            "found %u skeleton literals in %d constraints",
            ids->count,
            count);

#if 0
  lglsetopt (lgl, "clim", 10000);
  res = lglsat (lgl);
#else
  res = lglsimp (lgl, 0);
#endif

  if (btor->verbosity)
  {
    btor_msg (btor, 1, "skeleton preprocessing result %d", res);
    lglstats (lgl);
  }

  fixed = 0;

  if (res == 20)
  {
    btor_msg (btor, 1, "skeleton inconsistent");
    btor->inconsistent = 1;
  }
  else
  {
    assert (res == 0 || res == 10);
    for (b = ids->first; b; b = b->next)
    {
      exp = b->key;
      assert (!BTOR_IS_INVERTED_NODE (exp));
      lit = process_skeleton_tseitin_lit (ids, exp);
      val = lglfixed (lgl, lit);
      if (val)
      {
        if (!btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp)
            && !btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                             exp))
        {
          if (val < 0) exp = BTOR_INVERT_NODE (exp);
          add_constraint (btor, exp);
          btor->stats.skeleton_constraints++;
          fixed++;
        }
      }
      else
      {
        assert (
            !btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp));
        assert (!btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                              exp));
      }
    }
  }

  btor_delete_ptr_hash_table (ids);
  lglrelease (lgl);

  delta = btor_time_stamp () - start;
  btor->time.skel += delta;
  btor_msg (
      btor,
      1,
      "skeleton preprocessing produced %d new constraints in %.1f seconds",
      fixed,
      delta);
}

/*------------------------------------------------------------------------*/
#endif /* BTOR_DO_NOT_PROCESS_SKELETON */
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

  BtorPtrHashBucket *bucket;
  BtorNodePair *pair;

  for (bucket = btor->cache->first; bucket; bucket = bucket->next)
  {
    pair = (BtorNodePair *) bucket->key;
    btor_release_exp (btor, (BtorNode *) bucket->data.asPtr);
    delete_exp_pair (btor, pair);
  }
  btor_delete_ptr_hash_table (btor->cache);
  btor->cache = 0;
}

static void
beta_reduce_applies_on_lambdas (Btor *btor)
{
  double start = btor_time_stamp (), delta;
  assert (btor);

  BtorPtrHashTable *apps;
  BtorPtrHashBucket *b;
  BtorNode *app, *fun;
  BtorPartialParentIterator it;
  BtorMemMgr *mm;

  if (btor->lambdas->count == 0) return;

  mm   = btor->mm;
  apps = btor_new_ptr_hash_table (mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);

  /* collect function applications */
  for (b = btor->lambdas->first; b; b = b->next)
  {
    fun = BTOR_REAL_ADDR_NODE ((BtorNode *) b->key);
    init_apply_parent_iterator (&it, fun);
    while (has_next_parent_apply_parent_iterator (&it))
    {
      app = next_parent_apply_parent_iterator (&it);

      if (btor_find_in_ptr_hash_table (apps, app)) continue;

      if (!app->parameterized)
      // FIXME: only beta reduce not parameterized reads
      //	      || BTOR_REAL_ADDR_NODE (read->e[0])->refs == 1)
      {
        assert (!app->parameterized || app->e[0]->refs == 1);
        btor_insert_in_ptr_hash_table (apps, app);
      }
    }
  }

  // TODO: do we have to release the cache for lambdas that are only referenced
  // by the cache itself? maybe a cleanup cache function?
  btor_msg (btor,
            1,
            "starting to beta reduce %d lamba with %d applications",
            btor->lambdas->count,
            apps->count);
  substitute_and_rebuild (btor, apps, 1);
  btor_delete_ptr_hash_table (apps);
  delta = btor_time_stamp () - start;
  btor->time.betareduce += delta;
  btor_msg (btor, 1, "beta reduced all lambdas in %.1f seconds", delta);
}

#if 0
static void
merge_lambda_chains (Btor * btor)
{
  assert (btor);

  double start, delta;
  int chain_depth, start_lambdas, delta_lambdas;
  BtorNode *cur, *parent, *subst, *param, *lambda;
  BtorMemMgr *mm;
  BtorPtrHashBucket *b;
  BtorNodePtrQueue queue;
  BtorNodePtrStack stack, unmark_stack, params;

  mm = btor->mm;
  BTOR_INIT_QUEUE (queue);
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (unmark_stack);

  start = btor_time_stamp ();
  btor_init_substitutions (btor);

  for (b = btor->lambdas->first; b; b = b->next)
    {
      cur = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (cur));

      if (BTOR_REAL_ADDR_NODE (cur->e[1])->lambda_below)
	continue;

      BTOR_ENQUEUE (mm, queue, cur);
    }

  for (b = btor->lambdas->first; b; b = b->next)
    {
      cur = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (cur));

      if (!BTOR_REAL_ADDR_NODE (cur->e[1])->lambda_below)
	continue;

      BTOR_ENQUEUE (mm, queue, cur);
    }

  start_lambdas = btor->lambdas->count;
  while (!BTOR_EMPTY_QUEUE (queue))
    {
      cur = BTOR_DEQUEUE (queue);
      BTOR_PUSH_STACK (mm, stack, cur);

      /* look for a lambda chain */
      chain_depth = 0;
      while (!BTOR_EMPTY_STACK (stack))
	{
	  cur = BTOR_POP_STACK (stack);
	  assert (BTOR_IS_REGULAR_NODE (cur));
	  assert (BTOR_IS_LAMBDA_NODE (cur));

	  if (cur->parents != 1 || cur->aux_mark)
	    break;

	  cur->aux_mark = 1;
	  BTOR_PUSH_STACK (mm, unmark_stack, cur);

	  parent = BTOR_REAL_ADDR_NODE (cur->first_parent);
	  assert (parent);
	  assert (BTOR_IS_REGULAR_NODE (parent));

	  /* parent is part of a nested lambda chain */
	  if (BTOR_IS_LAMBDA_NODE (parent))
	    {
	      assert (BTOR_IS_NESTED_LAMBDA_NODE (parent));
	      cur->chain = 1;
	      BTOR_PUSH_STACK (mm, stack, parent);
	      continue;
	    }

	  assert (BTOR_IS_APPLY_NODE (parent));

	  if (!parent->parameterized)
	    break;

	  // TODO: should we use a flag or a hash table for marking lambda
	  //       nodes in a chain?
	  /* this lambda has only one parameterized application and thus,
	   * we can merge it with the parent lambda */
	  cur->chain = 1;
	  chain_depth++;
	  btor->stats.lambdas_merged++;
	  /* mark all nested lambdas below to be part of the chain, otherwise
	   * beta-reduction would stop at those lambdas */
	  if (BTOR_IS_NESTED_LAMBDA_NODE (cur))
	    {
	      assert (BTOR_IS_FIRST_NESTED_LAMBDA (cur));
	      lambda = cur;
	      while (BTOR_IS_LAMBDA_NODE (lambda))
		{
		  assert (BTOR_IS_NESTED_LAMBDA_NODE (lambda));
		  lambda->chain = 1;
		  lambda = lambda->e[1];
		}
	    }
	  BTORLOG ("merge: %s", node2string (cur));

	  /* get parent lambda */
	  assert (BTOR_EMPTY_STACK (params));
	  find_nodes_dfs (btor, parent->e[1], &params, findfun_param,
			  skipfun_param);
//	  assert (BTOR_COUNT_STACK (params) == 1);
	  int num_params = BTOR_COUNT_STACK (params);

	  // TODO: handle multiple params
	  // if we have multiple params we found a nested function, we have to
	  // order params in defined lambda order
	  while (!BTOR_EMPTY_STACK (params))
	    {
	      param = BTOR_POP_STACK (params);
	      assert (BTOR_IS_REGULAR_NODE (param));
	      assert (BTOR_IS_PARAM_NODE (param));
	      lambda = (BtorNode *) BTOR_PARAM_GET_LAMBDA_NODE (param);
	      assert (BTOR_IS_LAMBDA_NODE (lambda));
	      assert (num_params == 1 || BTOR_IS_NESTED_LAMBDA_NODE (lambda));
	      if (num_params == 1 || BTOR_IS_FIRST_NESTED_LAMBDA (lambda))
		BTOR_PUSH_STACK (mm, stack, lambda);
	    }
	}

      BTOR_RESET_STACK (stack);
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_LAMBDA_NODE (cur));

      if (chain_depth == 0)
	continue;

      /* cur is the start of the lambda chain */
//      cur->chain = 1;
      if (BTOR_IS_NESTED_LAMBDA_NODE (cur))
	{
	  assert (BTOR_IS_FIRST_NESTED_LAMBDA (cur));
	  lambda = cur;
	  while (BTOR_IS_LAMBDA_NODE (lambda))
	    {
	      assert (BTOR_IS_NESTED_LAMBDA_NODE (lambda));
	      lambda->chain = 1;
	      lambda = lambda->e[1];
	    }
	  // TODO: we cannot beta reduce the start of the nested lambdas,
	  //       we have to reduce the function body, substitute it and
	  //       rebuild everything
	  cur = lambda;
	}
      else
	cur->chain = 1;

      /* merge found lambda chain */
//      param = cur->e[0];
//      btor_assign_param (btor, cur, param);
      subst = btor_beta_reduce_chains (btor, cur);
//      btor_unassign_params (btor, cur);

      // TODO: update substitution
      btor_insert_substitution (btor, cur, subst, 1);
      btor_release_exp (btor, subst);
      btor->stats.lambdas_merged++;
      btor->stats.lambda_chains_merged++;
    }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    {
      cur = BTOR_POP_STACK (unmark_stack);
      assert (BTOR_IS_REGULAR_NODE (cur));
      cur->aux_mark = 0;
    }
  BTOR_RELEASE_STACK (mm, unmark_stack);

  substitute_and_rebuild (btor, btor->substitutions, 0);
  delta_lambdas = start_lambdas - btor->lambdas->count;

  BTOR_RELEASE_QUEUE (mm, queue);
  BTOR_RELEASE_STACK (mm, params);
  BTOR_RELEASE_STACK (mm, stack);
  btor_delete_substitutions (btor);
  delta = btor_time_stamp () - start;
  btor_msg (btor, 1, "merged %d lambdas in %.2f seconds",
		delta_lambdas, delta);
}
#endif

int
btor_simplify (Btor *btor)
{
  int rounds;
  double start, delta;
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  int skelrounds = 0;
#endif

  assert (btor);
  if (btor->inconsistent) return BTOR_UNSAT;

  //  if (btor->rewrite_level <= 1 && !btor->beta_reduce_all)
  //    return;

  rounds = 0;
  start  = btor_time_stamp ();

  init_cache (btor);

  do
  {
    rounds++;
    assert (check_all_hash_tables_proxy_free_dbg (btor));
    assert (check_all_hash_tables_simp_free_dbg (btor));
    assert (check_unique_table_children_proxy_free_dbg (btor));
    if (btor->rewrite_level > 1)
    {
      substitute_var_exps (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));

      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) break;

      process_embedded_constraints (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));

      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) continue;
    }

#ifndef BTOR_DO_NOT_ELIMINATE_SLICES
    if (btor->rewrite_level > 2 && !btor->inc_enabled)
    {
      eliminate_slices_on_bv_vars (btor);
      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) continue;

      if (btor->embedded_constraints->count) continue;
    }
#endif

#ifndef BTOR_DO_NOT_PROCESS_SKELETON
    if (btor->rewrite_level > 2)
    {
      skelrounds++;
      if (skelrounds <= 1)  // TODO only one?
      {
        process_skeleton (btor);
        assert (check_all_hash_tables_proxy_free_dbg (btor));
        assert (check_all_hash_tables_simp_free_dbg (btor));
        assert (check_unique_table_children_proxy_free_dbg (btor));
        if (btor->inconsistent) break;
      }

      if (btor->varsubst_constraints->count) continue;

      if (btor->embedded_constraints->count) continue;
    }
#endif

#if 0
      if (btor->rewrite_level > 2)
	{
	  merge_lambda_chains (btor);
	}
#endif

    if (btor->varsubst_constraints->count) continue;

    if (btor->embedded_constraints->count) continue;

    /* rewrite/beta-reduce applies on lambdas */
    if (btor->beta_reduce_all)
    {
      beta_reduce_applies_on_lambdas (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));
    }
  } while (btor->varsubst_constraints->count
           || btor->embedded_constraints->count);

  release_cache (btor);

  delta = btor_time_stamp () - start;
  btor->time.rewrite += delta;
  btor_msg (btor, 1, "%d rewriting rounds in %.1f seconds", rounds, delta);

  if (btor->inconsistent)
    return BTOR_UNSAT;
  else if (btor->unsynthesized_constraints->count == 0u
           && btor->synthesized_constraints->count == 0u)
    return BTOR_SAT;

  return BTOR_UNKNOWN;
}

static void
mark_synth_mark_exp (Btor *btor, BtorNode *exp, int new_mark)
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
  goto MARK_SYNTH_MARK_NODE_ENTER_WITHOUT_POP;

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
  MARK_SYNTH_MARK_NODE_ENTER_WITHOUT_POP:
    if (cur->synth_mark != new_mark)
    {
      cur->synth_mark = new_mark;
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

// TODO: stop synthesize at lambdas
static void
synthesize_exp (Btor *btor, BtorNode *exp, BtorPtrHashTable *backannotation)
{
  BtorNodePtrStack exp_stack;
  BtorNode *cur;
  BtorAIGVec *av0, *av1, *av2;
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorPtrHashBucket *b;
  char *indexed_name;
  const char *name;
  unsigned int count;
  int same_children_mem, i, len;
  int invert_av0 = 0;
  int invert_av1 = 0;
  int invert_av2 = 0;

  assert (btor);
  assert (exp);

  mm    = btor->mm;
  avmgr = btor->avmgr;
  count = 0;

  BTOR_INIT_STACK (exp_stack);
  BTOR_PUSH_STACK (mm, exp_stack, exp);
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  while (!BTOR_EMPTY_STACK (exp_stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (exp_stack));

    assert (cur->synth_mark >= 0);
    assert (cur->synth_mark <= 2);

    if (BTOR_IS_SYNTH_NODE (cur)) continue;

    if (cur->synth_mark >= 2) continue;

    count++;

    if (cur->synth_mark == 0)
    {
      /* we need to mark nodes reachable on-the-fly during
       * lazy_synthesize_and_encode_*_exp, do not remove! */
      cur->reachable = 1;

      if (BTOR_IS_BV_CONST_NODE (cur))
      {
        cur->av = btor_const_aigvec (avmgr, cur->bits);
        BTORLOG ("  synthesized: %s", node2string (cur));
      }
      else if (BTOR_IS_BV_VAR_NODE (cur))
      {
        cur->av = btor_var_aigvec (avmgr, cur->len);
        BTORLOG ("  synthesized: %s", node2string (cur));
        if (backannotation)
        {
          // TODO param handling?
          name = btor_get_symbol_exp (btor, cur);
          len  = (int) strlen (name) + 40;
          if (cur->len > 1)
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
            assert (cur->len == 1);
            b = btor_insert_in_ptr_hash_table (backannotation,
                                               cur->av->aigs[0]);
            assert (b->key == cur->av->aigs[0]);
            b->data.asStr = btor_strdup (mm, name);
          }
        }
      }
      else if (BTOR_IS_ARRAY_VAR_NODE (cur))
      {
        /* nothing to synthesize for array base case */
      }
      else if (BTOR_IS_LAMBDA_NODE (cur))
      {
        // TODO: do we have to synthesize the children?
        // this will be done with lazy_synth anyways
        goto REGULAR_CASE;
      }
      else
      {
        /* Writes and Lambda expressions cannot be reached directly,
         * hence we stop the synthesis as soon as we reach reads or
         * array equalities.  If we synthesize writes later, we only
         * synthesize its index and value, but not the write itself.
         * If there are no reads or array equalities on a write, then
         * it is not reachable. (Lambdas are treated similarly.)
         */
        //	      assert (!BTOR_IS_LAMBDA_NODE (cur));

        /* Atomic arrays and array conditionals should also not be
         * reached directly.
         */
        //	      assert (!BTOR_IS_ARRAY_VAR_NODE (cur));
        assert (!BTOR_IS_FUN_NODE (cur));

        /* special cases */
        if (BTOR_IS_APPLY_NODE (cur) && !cur->parameterized)
        {
          cur->av = btor_var_aigvec (avmgr, cur->len);
          BTORLOG ("  synthesized: %s", node2string (cur));
          assert (BTOR_IS_REGULAR_NODE (cur->e[0]));
          assert (BTOR_IS_FUN_NODE (cur->e[0]));
          goto REGULAR_CASE;
        }
#if 0
	      else if (BTOR_IS_ARRAY_EQ_NODE (cur) && !cur->parameterized)
		{
		  /* Generate virtual reads and create AIG variable for
		   * array equality.
		   */
		  synthesize_array_equality (btor, cur);
		  BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
		  BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
		  goto REGULAR_CASE;
		}
#endif
        else
        {
        REGULAR_CASE:
          // TODO: get rid of no_synth (use BTOR_IS_ARGS_NODE instead)
          /* always skip lambda and parameterized nodes */
          if (BTOR_IS_LAMBDA_NODE (cur) || cur->parameterized || cur->no_synth)
            cur->synth_mark = 2;
          else
            cur->synth_mark = 1;

          BTOR_PUSH_STACK (mm, exp_stack, cur);
          for (i = cur->arity - 1; i >= 0; i--)
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[i]);
        }
      }
    }
    else
    {
      assert (cur->synth_mark == 1);
      cur->synth_mark = 2;
      assert (!BTOR_IS_APPLY_NODE (cur));
      assert (!BTOR_IS_LAMBDA_NODE (cur));
      assert (!cur->parameterized);

      if (cur->arity == 1)
      {
        assert (cur->kind == BTOR_SLICE_NODE);
        invert_av0 = BTOR_IS_INVERTED_NODE (cur->e[0]);
        av0        = BTOR_REAL_ADDR_NODE (cur->e[0])->av;
        if (invert_av0) btor_invert_aigvec (avmgr, av0);
        cur->av = btor_slice_aigvec (avmgr, av0, cur->upper, cur->lower);
        BTORLOG ("  synthesized: %s", node2string (cur));
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
        BTORLOG ("  synthesized: %s", node2string (cur));

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
          BTORLOG ("  synthesized: %s", node2string (cur));
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
    }
  }

  BTOR_RELEASE_STACK (mm, exp_stack);
  mark_synth_mark_exp (btor, exp, 0);

  if (count > 0 && btor->verbosity > 3)
    btor_msg (btor, 3, "synthesized %u expressions into AIG vectors", count);
}

static void
synthesize_all_var_rhs (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorNode *cur, *real_cur;

  assert (btor);
  assert (btor->model_gen);

  for (b = btor->var_rhs->first; b; b = b->next)
  {
    cur      = (BtorNode *) b->key;
    cur      = btor_simplify_exp (btor, cur);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!BTOR_IS_ARRAY_NODE (real_cur));
    if (real_cur->vread) continue;

    synthesize_exp (btor, cur, 0);

    if (!real_cur->tseitin)
    {
      btor_aigvec_to_sat_tseitin (btor->avmgr, real_cur->av);
      real_cur->tseitin = 1;
    }
  }
}

static void
synthesize_all_array_rhs (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorNode *cur;

  assert (btor);
  assert (btor->model_gen);

  for (b = btor->array_rhs->first; b; b = b->next)
  {
    cur = (BtorNode *) b->key;
    cur = btor_simplify_exp (btor, cur);
    assert (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (cur)));
    synthesize_exp (btor, cur, 0);
  }
}

static void
synthesize_all_reads (Btor *btor)
{
  BtorNode *n;
  int i;
  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (n = btor->nodes_unique_table.chains[i]; n; n = n->next)
      if (BTOR_IS_READ_NODE (n)) synthesize_exp (btor, n, 0);
}

#if 0
// TODO: check if needed
static void
synthesize_all_applies (Btor * btor)
{
  BtorNode *n;
  int i;
  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (n = btor->nodes_unique_table.chains[i]; n; n = n->next)
      if (BTOR_IS_APPLY_NODE (n))
	synthesize_exp (btor, n, 0);
}
#endif

/* Mark all reachable expressions as reachable, reset reachable flag for all
 * previously reachable expressions that became unreachable due to rewriting. */
static void
update_reachable (Btor *btor)
{
  assert (btor);

  int i;
  BtorNode *exp;
  BtorPtrHashBucket *b;

  assert (check_unique_table_mark_unset_dbg (btor));
  assert (btor->unsynthesized_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);
  assert (btor->varsubst_constraints->count == 0);

  for (b = btor->synthesized_constraints->first; b; b = b->next)
    btor_mark_exp (btor, (BtorNode *) b->key, 1);
  for (b = btor->lod_cache->first; b; b = b->next)
    btor_mark_exp (btor, (BtorNode *) b->key, 1);

  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    if (!(exp = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;
    exp->reachable = exp->mark;
    exp->mark      = 0;
  }
}

/* makes assumptions to the SAT solver */
static int
add_again_assumptions (Btor *btor)
{
  BtorNode *exp;
  BtorPtrHashBucket *b;
  BtorAIG *aig;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  assert (btor);
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  for (b = btor->assumptions->first; b; b = b->next)
  {
    assert (BTOR_REAL_ADDR_NODE ((BtorNode *) b->key)->len == 1);
    exp = (BtorNode *) b->key;
    exp = btor_simplify_exp (btor, exp);
    aig = btor_exp_to_aig (btor, exp);
    if (aig == BTOR_AIG_FALSE) return 1;
    btor_aig_to_sat (amgr, aig);
    if (aig != BTOR_AIG_TRUE)
    {
      assert (BTOR_REAL_ADDR_AIG (aig)->cnf_id != 0);
      btor_assume_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
      btor_release_aig (amgr, aig);
    }
  }

  return 0;
}

static int
btor_timed_sat_sat (Btor *btor, int limit)
{
  double start, delta;
  BtorSATMgr *smgr;
  int res;
  smgr  = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  start = btor_time_stamp ();
  res   = btor_sat_sat (smgr, limit);
  delta = btor_time_stamp () - start;
  btor->time.sat += delta;
  btor_msg (btor, 2, "SAT solver returns %d after %.1f seconds", res, delta);
  return res;
}

/* updates SAT assignments, reads assumptions and
 * returns if an assignment has changed
 */
static int
update_sat_assignments (Btor *btor)
{
  int result, found_assumption_false;
  BtorSATMgr *smgr = 0;
  assert (btor);
  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  found_assumption_false = add_again_assumptions (btor);
  assert (!found_assumption_false);
  result = btor_timed_sat_sat (btor, -1);
  assert (result == BTOR_SAT);
  return found_assumption_false || (result != BTOR_SAT)
         || btor_changed_sat (smgr);
}

/**
 * Collect all top functions.
 *
 * A top function does not have parameterized applies and lambdas as parent.
 */
static void
search_top_functions (Btor *btor, BtorNodePtrStack *top_funs)
{
  assert (btor);
  assert (top_funs);
  assert (BTOR_EMPTY_STACK (*top_funs));

  int is_top;
  BtorMemMgr *mm;
  BtorNode *cur, *cur_parent;
  BtorPtrHashTable *table;
  BtorPtrHashBucket *bucket;
  BtorFullParentIterator it;

  mm = btor->mm;

  for (table = btor->array_vars; table;
       table = table == btor->array_vars ? btor->lambdas : 0)
  {
    for (bucket = table->first; bucket; bucket = bucket->next)
    {
      cur = (BtorNode *) bucket->key;
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_FUN_NODE (cur));

      /* we only consider reachable nodes */
      if (!cur->reachable) continue;

      init_full_parent_iterator (&it, cur);

      is_top = 1;
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (cur_parent));

        if (!cur_parent->reachable) continue;

        if ((BTOR_IS_APPLY_NODE (cur_parent) && cur_parent->parameterized)
            || BTOR_IS_LAMBDA_NODE (cur_parent))
        {
          is_top = 0;
          break;
        }
      }

      if (is_top) BTOR_PUSH_STACK (mm, *top_funs, cur);
    }
  }
}

static int
findfun_param_apply (BtorNode *exp)
{
  assert (exp);
  exp = BTOR_REAL_ADDR_NODE (exp);
  return BTOR_IS_APPLY_NODE (exp) && exp->parameterized;
}

static int
skipfun_tseitin (BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->tseitin;
}

static void
find_nodes_dfs (Btor *btor,
                BtorNode *exp,
                BtorNodePtrStack *results,
                int (*findfun) (BtorNode *),
                int (*skipfun) (BtorNode *))
{
  assert (btor);
  assert (exp);
  assert (results);
  assert (findfun);

  int i;
  double start;
  BtorNode *cur;
  BtorNodePtrStack work_stack, unmark_stack;
  BtorMemMgr *mm;

  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  start = btor_time_stamp ();
  mm    = btor->mm;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_PUSH_STACK (mm, work_stack, exp);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));

    if (cur->mark || (skipfun && skipfun (cur))) continue;

    cur->mark = 1;
    BTOR_PUSH_STACK (mm, unmark_stack, cur);

    if (findfun (cur))
    {
      BTOR_PUSH_STACK (mm, *results, cur);
      BTORLOG ("  found: %s", node2string (cur));
      continue;
    }

    for (i = 0; i < cur->arity; i++)
      BTOR_PUSH_STACK (mm, work_stack, cur->e[i]);
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    cur->mark = 0;
  }

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, unmark_stack);
  btor->time.find_dfs += btor_time_stamp () - start;
}

static void
check_not_simplified_or_const (Btor *btor, BtorNode *exp)
{
#ifndef NDEBUG
  assert (btor);
  assert (exp);

  exp = BTOR_REAL_ADDR_NODE (exp);

  if (!exp->simplified) return;

  assert (exp->len == 1);
  while (exp->simplified) exp = BTOR_REAL_ADDR_NODE (exp->simplified);
  assert (BTOR_IS_BV_CONST_NODE (exp));
#else
  (void) btor;
  (void) exp;
#endif
}

/* Compares the assignments of two expressions. */
static int
compare_assignments (BtorNode *exp1, BtorNode *exp2)
{
  int return_val, val1, val2, i, len;
  Btor *btor;
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  assert (exp1);
  assert (exp2);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp1)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp2)));
  assert (BTOR_REAL_ADDR_NODE (exp1)->len == BTOR_REAL_ADDR_NODE (exp2)->len);
  assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (exp1)));
  assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (exp2)));
  btor = BTOR_REAL_ADDR_NODE (exp1)->btor;
  assert (btor);
  return_val = 0;
  avmgr      = btor->avmgr;
  amgr       = btor_get_aig_mgr_aigvec_mgr (avmgr);
  av1        = BTOR_REAL_ADDR_NODE (exp1)->av;
  av2        = BTOR_REAL_ADDR_NODE (exp2)->av;
  assert (av1->len == av2->len);
  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_NODE (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_NODE (exp2, av2->aigs[i]);

    val1 = btor_get_assignment_aig (amgr, aig1);
    assert (val1 == -1 || val1 == 1);

    val2 = btor_get_assignment_aig (amgr, aig2);
    assert (val2 == -1 || val2 == 1);

    if (val1 < val2)
    {
      return_val = -1;
      break;
    }

    if (val2 < val1)
    {
      return_val = 1;
      break;
    }
  }
  return return_val;
}

static int
compare_argument_assignments (BtorNode *e0, BtorNode *e1)
{
  assert (BTOR_IS_REGULAR_NODE (e0));
  assert (BTOR_IS_REGULAR_NODE (e1));
  assert (BTOR_IS_ARGS_NODE (e0));
  assert (BTOR_IS_ARGS_NODE (e1));

  int equal;
  const char *avec0, *avec1;
  BtorNode *arg0, *arg1;
  Btor *btor;
  BtorArgsIterator it0, it1;
  btor = e0->btor;

  // TODO: check args num_args
  if (e0->len != e1->len) return 1;

  init_args_iterator (&it0, e0);
  init_args_iterator (&it1, e1);

  while (has_next_args_iterator (&it0))
  {
    assert (has_next_args_iterator (&it1));
    arg0 = next_args_iterator (&it0);
    arg1 = next_args_iterator (&it1);

    if (!BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (arg0)))
      avec0 = btor_eval_exp (btor, arg0);
    else
      avec0 = btor_bv_assignment_exp (btor, arg0);

    if (!BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (arg1)))
      avec1 = btor_eval_exp (btor, arg1);
    else
      avec1 = btor_bv_assignment_exp (btor, arg1);

    assert (avec0);
    assert (avec1);
    equal = strcmp (avec0, avec1) == 0;
    btor_freestr (btor->mm, (char *) avec0);
    btor_freestr (btor->mm, (char *) avec1);

    if (!equal) return 1;
  }

  return 0;
}

static unsigned int
hash_assignment_aux (BtorNode *exp)
{
  unsigned int hash;
  Btor *btor;
  BtorAIGVecMgr *avmgr;
  BtorNode *real_exp;
  BtorAIGVec *av;
  int invert_av;
  char *assignment;
  assert (exp);
  real_exp  = BTOR_REAL_ADDR_NODE (exp);
  btor      = real_exp->btor;
  avmgr     = btor->avmgr;
  av        = real_exp->av;
  invert_av = BTOR_IS_INVERTED_NODE (exp);
  if (invert_av) btor_invert_aigvec (avmgr, av);
  assignment = btor_assignment_aigvec (avmgr, av);
  hash       = btor_hashstr (assignment);
  btor_freestr (btor->mm, assignment);
  /* invert back if necessary */
  if (invert_av) btor_invert_aigvec (avmgr, av);
  return hash;
}

static unsigned int
hash_args (BtorNode *exp)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_ARGS_NODE (exp));

  int invert_av;
  char *assignment;
  unsigned int hash;
  Btor *btor;
  BtorNode *arg;
  BtorAIGVecMgr *avmgr;
  BtorAIGVec *av;
  BtorArgsIterator it;

  btor  = exp->btor;
  avmgr = btor->avmgr;

  init_args_iterator (&it, exp);
  hash = 0;
  while (has_next_args_iterator (&it))
  {
    arg       = next_args_iterator (&it);
    invert_av = BTOR_IS_INVERTED_NODE (arg);
    av        = BTOR_REAL_ADDR_NODE (arg)->av;
    assert (av);
    if (invert_av) btor_invert_aigvec (avmgr, av);
    assignment = btor_assignment_aigvec (avmgr, av);
    hash += btor_hashstr (assignment);
    btor_freestr (btor->mm, assignment);
    if (invert_av) btor_invert_aigvec (avmgr, av);
  }
  return hash;
}

static unsigned int
hash_assignment (BtorNode *exp)
{
  if (BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (exp))) return hash_args (exp);
  return hash_assignment_aux (exp);
}

static int
lazy_synthesize_and_encode_var_exp (Btor *btor, BtorNode *var, int force_update)
{
  assert (btor);
  assert (var);
  assert (BTOR_IS_REGULAR_NODE (var));
  assert (BTOR_IS_BV_VAR_NODE (var));

  double start;
  int changed_assignments, update;
  BtorAIGVecMgr *avmgr = 0;

  if (var->tseitin) return 0;

  start               = btor_time_stamp ();
  changed_assignments = 0;
  update              = 0;
  avmgr               = btor->avmgr;
  BTORLOG ("%s: %s", __FUNCTION__, node2string (var));

  /* synthesize and encode var */
  if (!BTOR_IS_SYNTH_NODE (var)) synthesize_exp (btor, var, 0);

  if (!var->tseitin)
  {
    update = 1;
    btor_aigvec_to_sat_tseitin (avmgr, var->av);
    var->tseitin = 1;
    BTORLOG ("  encode: %s", node2string (var));
  }

  /* update assignments if necessary */
  if (update && force_update)
    changed_assignments = update_sat_assignments (btor);

  // TODO: assignment should never change when encoding vars
  //	   (since unconstrained)
  if (changed_assignments) btor->stats.synthesis_inconsistency_var++;

  btor->time.enc_var += btor_time_stamp () - start;
  return changed_assignments;
}

/* synthesize and encode apply node and all of its arguments into SAT.
 * returns 0 if encoding changed current assignments.
 */
static int
lazy_synthesize_and_encode_apply_exp (Btor *btor,
                                      BtorNode *app,
                                      int force_update)
{
  assert (btor);
  assert (app);
  assert (BTOR_IS_REGULAR_NODE (app));
  assert (BTOR_IS_APPLY_NODE (app));
  assert (BTOR_IS_REGULAR_NODE (app->e[1]));
  assert (BTOR_IS_ARGS_NODE (app->e[1]));

  double start;
  int changed_assignments, update;
  BtorNode *arg;
  BtorAIGVecMgr *avmgr = 0;
  BtorArgsIterator it;

  if (app->lazy_tseitin) return 0;

  start               = btor_time_stamp ();
  changed_assignments = 0;
  update              = 0;
  avmgr               = btor->avmgr;
  BTORLOG ("%s: %s", __FUNCTION__, node2string (app));

  init_args_iterator (&it, app->e[1]);

  /* synthesize and encode apply node an all of its arguments */
  while (has_next_args_iterator (&it))
  {
    arg = next_args_iterator (&it);
    assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (arg)));
    if (!BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (arg)))
      synthesize_exp (btor, arg, 0);

    if (!BTOR_REAL_ADDR_NODE (arg)->tseitin)
    {
      update = 1;
      btor_aigvec_to_sat_tseitin (avmgr, BTOR_REAL_ADDR_NODE (arg)->av);
      BTOR_REAL_ADDR_NODE (arg)->tseitin = 1;
      BTORLOG ("  encode: %s", node2string (arg));
    }
  }

  /* synthesize and encode apply expressions */
  if (!BTOR_IS_SYNTH_NODE (app)) synthesize_exp (btor, app, 0);

  if (!app->tseitin)
  {
    update = 1;
    btor_aigvec_to_sat_tseitin (avmgr, app->av);
    app->tseitin = 1;
    BTORLOG ("  encode: %s", node2string (app));
  }

  app->lazy_tseitin = 1;

  /* update assignments if necessary */
  if (update && force_update)
    changed_assignments = update_sat_assignments (btor);

  if (changed_assignments) btor->stats.synthesis_inconsistency_apply++;

  btor->time.enc_app += btor_time_stamp () - start;
  return changed_assignments;
}

static int
lazy_synthesize_and_encode_lambda_exp (Btor *btor,
                                       BtorNode *lambda_exp,
                                       int force_update)
{
  assert (btor);
  assert (lambda_exp);
  assert (BTOR_IS_REGULAR_NODE (lambda_exp));
  assert (BTOR_IS_LAMBDA_NODE (lambda_exp));

  double start;
  int changed_assignments, update, i;
  BtorNodePtrStack work_stack, unmark_stack;
  BtorNode *cur;
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;

  // TODO: remove lazy_tseitin
  if (lambda_exp->lazy_tseitin) return 0;

  start               = btor_time_stamp ();
  mm                  = btor->mm;
  avmgr               = btor->avmgr;
  changed_assignments = 0;
  update              = 0;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);

  BTORLOG ("%s: %s", __FUNCTION__, node2string (lambda_exp));

  cur = BTOR_REAL_ADDR_NODE (BTOR_LAMBDA_GET_BODY (lambda_exp));

  if (!BTOR_IS_SYNTH_NODE (cur)) synthesize_exp (btor, cur, 0);

  BTOR_PUSH_STACK (mm, work_stack, cur);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_POP_STACK (work_stack);
    assert (cur);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (cur->tseitin || cur->mark) continue;

    /* do not encode expressions that are not in the scope of 'lambda_exp' */
    if (BTOR_IS_FUN_NODE (cur) && !cur->parameterized) continue;

    cur->mark = 1;
    BTOR_PUSH_STACK (mm, unmark_stack, cur);

    if (!BTOR_IS_ARGS_NODE (cur) && !BTOR_IS_LAMBDA_NODE (cur)
        && !cur->parameterized)
    {
      assert (BTOR_IS_SYNTH_NODE (cur));
      assert (!cur->tseitin);
      BTORLOG ("  encode: %s", node2string (cur));
      update = 1;
      btor_aigvec_to_sat_tseitin (avmgr, cur->av);
      cur->tseitin = 1;
    }

    for (i = 0; i < cur->arity; i++)
      BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (cur->e[i]));
  }
  BTOR_RELEASE_STACK (mm, work_stack);

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (cur->mark);
    cur->mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);

  /* set tseitin flag of lambda expression to indicate that it has been
   * lazily synthesized already */
  lambda_exp->tseitin      = 1;
  lambda_exp->lazy_tseitin = 1;

  if (update && force_update)
    changed_assignments = update_sat_assignments (btor);

  if (changed_assignments) btor->stats.synthesis_inconsistency_lambda++;

  btor->time.enc_lambda += btor_time_stamp () - start;
  return changed_assignments;
}

static void
collect_premisses (Btor *btor,
                   BtorNode *from,
                   BtorNode *to,
                   BtorNode *args,
                   BtorPtrHashTable *bconds_sel1,
                   BtorPtrHashTable *bconds_sel2)
{
  assert (btor);
  assert (from);
  assert (to);
  assert (bconds_sel1);
  assert (bconds_sel2);
  assert (BTOR_IS_REGULAR_NODE (from));
  assert (BTOR_IS_REGULAR_NODE (args));
  assert (BTOR_IS_ARGS_NODE (args));
  assert (BTOR_IS_REGULAR_NODE (to));

  BTORLOG ("%s: %s, %s, %s",
           __FUNCTION__,
           node2string (from),
           node2string (to),
           node2string (args));

#ifndef NDEBUG
  int found = 0;
#endif
  int i;
  BtorMemMgr *mm;
  BtorNode *fun, *result, *cond, *param, *arg;
  BtorNodePtrStack prop_stack;
  BtorPtrHashTable *cond_sel1, *cond_sel2, *c, *r;
  BtorPtrHashBucket *b;
  BtorParamCacheTuple *t;
  BtorParameterizedIterator it;

  mm = btor->mm;
  cond_sel1 =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_param_cache_tuple,
                               (BtorCmpPtr) btor_compare_param_cache_tuple);
  cond_sel2 =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_param_cache_tuple,
                               (BtorCmpPtr) btor_compare_param_cache_tuple);

  if (BTOR_IS_APPLY_NODE (from))
  {
    assert (BTOR_IS_REGULAR_NODE (to));
    assert (BTOR_IS_FUN_NODE (to));

    // TODO: get rid of stack
    BTOR_INIT_STACK (prop_stack);
    BTOR_PUSH_STACK (mm, prop_stack, from->e[0]);

    while (!BTOR_EMPTY_STACK (prop_stack))
    {
      fun = BTOR_POP_STACK (prop_stack);
      assert (BTOR_IS_REGULAR_NODE (fun));
      assert (BTOR_IS_FUN_NODE (fun));

      if (fun == to)
      {
#ifndef NDEBUG
        found = 1;
#endif
        break;
      }

      btor_assign_args (btor, fun, args);
      result =
          btor_beta_reduce_partial_collect (btor, fun, cond_sel1, cond_sel2);
      btor_unassign_params (btor, fun);

      result = BTOR_REAL_ADDR_NODE (result);
      assert (BTOR_IS_APPLY_NODE (result));
      assert (result->e[1] == args);

      BTOR_PUSH_STACK (mm, prop_stack, result->e[0]);
      btor_release_exp (btor, result);
    }

    BTOR_RELEASE_STACK (mm, prop_stack);
  }
  else
  {
    assert (BTOR_IS_LAMBDA_NODE (from));
    fun = from;

    btor_assign_args (btor, fun, args);
    result = btor_beta_reduce_partial_collect (btor, fun, cond_sel1, cond_sel2);
    btor_unassign_params (btor, fun);

    result = BTOR_REAL_ADDR_NODE (result);
    assert (result == to);
#ifndef NDEBUG
    found = 1;
#endif
    btor_release_exp (btor, result);
  }

  assert (found);

  for (c = cond_sel1, r = bconds_sel1; c && r;
       c = (c == cond_sel1) ? cond_sel2 : 0,
      r  = (r == bconds_sel1) ? bconds_sel2 : 0)
  {
    for (b = c->first; b; b = b->next)
    {
      assert (b->data.asPtr);
      t = (BtorParamCacheTuple *) b->key;
      assert (t);
      cond = (BtorNode *) b->data.asPtr;
      assert (cond);

      if (BTOR_REAL_ADDR_NODE (cond)->parameterized)
      {
        i = 0;
        init_parameterized_iterator (btor, &it, BTOR_REAL_ADDR_NODE (cond));
        assert (it.num_params == t->num_args);
        assert (has_next_parameterized_iterator (&it));
        while (has_next_parameterized_iterator (&it))
        {
          param = next_parameterized_iterator (&it);
          assert (param);
          assert (i < t->num_args);
          arg = t->args[i++];
          assert (arg);
          btor_assign_param (
              btor, (BtorNode *) BTOR_PARAM_GET_LAMBDA_NODE (param), arg);
        }

        result = btor_beta_reduce_partial (btor, cond, 0);
        BTORLOG ("collected %s: %s, result: %s",
                 (c == cond_sel1) ? "sel1" : "sel2",
                 node2string (cond),
                 node2string (result));

        init_parameterized_iterator (btor, &it, BTOR_REAL_ADDR_NODE (cond));
        while (has_next_parameterized_iterator (&it))
        {
          param = next_parameterized_iterator (&it);
          btor_unassign_params (
              btor, (BtorNode *) BTOR_PARAM_GET_LAMBDA_NODE (param));
        }
      }
      else
      {
        result = btor_copy_exp (btor, cond);
      }

      if (!btor_find_in_ptr_hash_table (r, result))
        btor_insert_in_ptr_hash_table (r, result);
      else
        btor_release_exp (btor, result);

      btor_delete_param_cache_tuple (btor, t);
    }
  }

  btor_delete_ptr_hash_table (cond_sel1);
  btor_delete_ptr_hash_table (cond_sel2);
}

static int
assignment_always_unequal (Btor *btor, BtorNode *exp1, BtorNode *exp2)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  int i, len, val1, val2;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;

  assert (btor);

  if (!BTOR_IS_SYNTH_NODE (exp1)) return 0;

  if (!BTOR_IS_SYNTH_NODE (exp2)) return 0;

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp1)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp2)));
  assert (BTOR_REAL_ADDR_NODE (exp1)->len == BTOR_REAL_ADDR_NODE (exp2)->len);

  av1 = BTOR_REAL_ADDR_NODE (exp1)->av;
  av2 = BTOR_REAL_ADDR_NODE (exp2)->av;

  if (!av1 || !av2) return 0;

  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_NODE (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_NODE (exp2, av2->aigs[i]);

    if (aig1 == BTOR_AIG_TRUE)
      val1 = 1;
    else if (aig1 == BTOR_AIG_FALSE)
      val1 = -1;
    else if (!BTOR_REAL_ADDR_AIG (aig1)->cnf_id)
      val1 = 0;
    else
      val1 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig1));

    if (val1 != 0) /* toplevel assigned or const */
    {
      if (aig2 == BTOR_AIG_TRUE)
        val2 = 1;
      else if (aig2 == BTOR_AIG_FALSE)
        val2 = -1;
      else if (!BTOR_REAL_ADDR_AIG (aig2)->cnf_id)
        val2 = 0;
      else
        val2 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig2));

      if (val2 != 0 && val1 != val2) return 1;
    }
  }
  return 0;
}

static int
assignment_always_equal (Btor *btor, BtorNode *exp1, BtorNode *exp2)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  int i, len, val1, val2;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;

  assert (btor);

  if (!BTOR_IS_SYNTH_NODE (exp1)) return 0;

  if (!BTOR_IS_SYNTH_NODE (exp2)) return 0;

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp1)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp2)));
  assert (BTOR_REAL_ADDR_NODE (exp1)->len == BTOR_REAL_ADDR_NODE (exp2)->len);

  av1 = BTOR_REAL_ADDR_NODE (exp1)->av;
  av2 = BTOR_REAL_ADDR_NODE (exp2)->av;
  if (!av1 || !av2) return 0;

  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_NODE (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_NODE (exp2, av2->aigs[i]);

    if (aig1 == BTOR_AIG_TRUE)
      val1 = 1;
    else if (aig1 == BTOR_AIG_FALSE)
      val1 = -1;
    else if (!BTOR_REAL_ADDR_AIG (aig1)->cnf_id)
      return 0;
    else
      val1 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig1));

    if (!val1) return 0;

    if (aig2 == BTOR_AIG_TRUE)
      val2 = 1;
    else if (aig2 == BTOR_AIG_FALSE)
      val2 = -1;
    else if (!BTOR_REAL_ADDR_AIG (aig2)->cnf_id)
      return 0;
    else
      val2 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig2));

    if (!val2) return 0;

    if (val1 != val2) return 0;
  }
  return 1;
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
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  exp = btor_simplify_exp (btor, exp);

  sign = 1;

  if (BTOR_IS_INVERTED_NODE (exp))
  {
    exp = BTOR_INVERT_NODE (exp);
    sign *= -1;
  }

  aig = btor_exp_to_aig (btor, exp);

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);

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

    if (!aig->cnf_id)
    {
      assert (!exp->tseitin);
      btor_aig_to_sat_tseitin (amgr, aig);
      exp->tseitin = 1;
    }

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

static void
add_new_exp_to_clause (Btor *btor,
                       BtorNode *exp,
                       int sign,
                       BtorIntStack *linking_clause)
{
  assert (btor);
  assert (exp);
  assert (linking_clause);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  int lit, false_lit, true_lit;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorNode *real_exp;

  mm        = btor->mm;
  amgr      = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr      = btor_get_sat_mgr_aig_mgr (amgr);
  true_lit  = smgr->true_lit;
  false_lit = -true_lit;
  exp       = btor_simplify_exp (btor, exp);
  real_exp  = BTOR_REAL_ADDR_NODE (exp);

  if (!btor_find_in_ptr_hash_table (btor->lod_cache, real_exp))
    btor_insert_in_ptr_hash_table (btor->lod_cache,
                                   btor_copy_exp (btor, real_exp));

  // TODO: simplifications?
  //	   a && 1: a
  //	   b && 1: b
  //	   a && 0 || 0 && b: 0
  //	   ...
  if (BTOR_IS_BV_EQ_NODE (real_exp))
  {
    if (assignment_always_unequal (btor, real_exp->e[0], real_exp->e[1]))
    {
      lit = false_lit;
      goto SIGN_AND_PUSH;
    }
    else if (assignment_always_equal (btor, real_exp->e[0], real_exp->e[1]))
    {
      lit = true_lit;
      goto SIGN_AND_PUSH;
    }
  }

  lit = exp_to_cnf_lit (btor, exp);

SIGN_AND_PUSH:
  lit *= sign;

  if (lit != false_lit && lit != true_lit)
    BTOR_PUSH_STACK (mm, *linking_clause, lit);
}

static void
add_eq_exp_to_clause (Btor *btor,
                      BtorNode *a,
                      BtorNode *b,
                      BtorIntStack *linking_clause)
{
  BtorNode *eq = btor_eq_exp (btor, a, b);
  add_new_exp_to_clause (btor, eq, 1, linking_clause);
  btor_release_exp (btor, eq);
}

static void
add_neq_exp_to_clause (Btor *btor,
                       BtorNode *a,
                       BtorNode *b,
                       BtorIntStack *linking_clause)
{
  BtorNode *eq = btor_eq_exp (btor, a, b);
  add_new_exp_to_clause (btor, eq, -1, linking_clause);
  btor_release_exp (btor, eq);
}

// TODO: update print function according to encode_lemma (new apply handling...)
#if 0
static void
print_lemma_dbg (Btor * btor,
		 BtorPtrHashTable * fun_apps,
		 BtorPtrHashTable * bconds_sel1,
		 BtorPtrHashTable * bconds_sel2,
		 BtorNode * app0, BtorNode * app1)
{
  int i;
  BtorNode *arg0, *arg1, *args0 = 0, *args1 = 0;
  BtorNode *cur, *cond;
  BtorPtrHashBucket *bucket;

  app0 = BTOR_REAL_ADDR_NODE (app0);
  app1 = BTOR_REAL_ADDR_NODE (app1);

  BTORLOG ("\e[1;32m");
  BTORLOG ("ENCODED LEMMA");
  BTORLOG ("  app0: %s", node2string (app0));
  BTORLOG ("  app1: %s", node2string (app1));

  if (BTOR_IS_APPLY_NODE (app0))
    args0 = app0->e[1];

  if (BTOR_IS_APPLY_NODE (app1))
    args1 = app1->e[1];

  if (args0 && args1)
    {
      BTORLOG ("   args: %s = %s", node2string (args0),
	       node2string (args1));
      assert (BTOR_IS_REGULAR_NODE (args0));
      assert (BTOR_IS_REGULAR_NODE (args1));
      assert (args0->arity == args1->arity);
      for (i = 0; i < args0->arity; i++)
	{
	  arg0 = args0->e[i];
	  arg1 = args1->e[i];
	  BTORLOG ("    %c%s = %c%s",
	      BTOR_IS_INVERTED_NODE (arg0) ? '-' : ' ', node2string (arg0),
	      BTOR_IS_INVERTED_NODE (arg1) ? '-' : ' ', node2string (arg1));
	}
    }

  BTORLOG ("  fun apps:");
  for (bucket = fun_apps->last; bucket; bucket = bucket->prev)
    {
      cur = (BtorNode *) bucket->key;
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_APPLY_NODE (cur));
      args0 = !BTOR_IS_APPLY_NODE (app1) ? app0->e[1] : app1->e[1];
      args1 = cur->e[1];
      assert (BTOR_IS_ARGS_NODE (args0));
      assert (BTOR_IS_ARGS_NODE (args1));
      assert (args0->arity == args1->arity);

      for (i = 0; i < args0->arity; i++)
	BTORLOG ("    %s = %s", node2string (args0->e[i]),
		 node2string (args1->e[i]));
    }

  BTORLOG ("  bv cond if:");
  for (bucket = bconds_sel1->last; bucket; bucket = bucket->prev)
    {
      cur = (BtorNode *) bucket->key;
      cond = cur->e[0];
      BTORLOG ("    %s", node2string (cond));
    }

  BTORLOG ("  bv cond else:");
  for (bucket = bconds_sel2->last; bucket; bucket = bucket->prev)
    {
      cur = (BtorNode *) bucket->key;
      cond = cur->e[0];
      BTORLOG ("    %s", node2string (cond));
    }

  BTORLOG ("  conclusion:");
  BTORLOG ("    %s = %s", node2string (app0), node2string (app1));

  BTORLOG (" \e[0;39m");
}
#endif

static void
encode_lemma (Btor *btor,
              BtorPtrHashTable *bconds_sel1,
              BtorPtrHashTable *bconds_sel2,
              BtorNode *a,
              BtorNode *b,
              BtorNode *args0,
              BtorNode *args1)
{
  assert (btor);
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
  assert (BTOR_IS_SYNTH_NODE (a));

  int k, val;
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorNode *arg0, *arg1;
  BtorNode *cond;
  BtorIntStack linking_clause;
  BtorPtrHashBucket *bucket;
  BtorArgsIterator it0, it1;

  mm    = btor->mm;
  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  BTOR_INIT_STACK (linking_clause);

  /* function congruence axiom conflict:
   *   apply arguments: a_0,...,a_n, b_0,...,b_n
   *   encode premisses: \forall i <= n . /\ a_i = b_i */
  if (args1)
  {
    assert (BTOR_IS_SYNTH_NODE (b));
    assert (((BtorArgsNode *) args0)->num_args
            == ((BtorArgsNode *) args1)->num_args);
    assert (args0->len == args1->len);

    init_args_iterator (&it0, args0);
    init_args_iterator (&it1, args1);

    while (has_next_args_iterator (&it0))
    {
      assert (has_next_args_iterator (&it1));
      arg0 = next_args_iterator (&it0);
      arg1 = next_args_iterator (&it1);
      add_neq_exp_to_clause (btor, arg0, arg1, &linking_clause);
      btor->stats.lemmas_size_sum += 1;
    }
  }
  /* else beta reduction conflict */

  /* encode conclusion a = b */
  add_eq_exp_to_clause (btor, a, b, &linking_clause);

  btor->stats.lemmas_size_sum += 1; /* a == b */
  btor->stats.lemmas_size_sum += bconds_sel1->count;
  btor->stats.lemmas_size_sum += bconds_sel2->count;

  /* premisses bv conditions:
   *   true conditions: c_0, ..., c_k
   *   encode premisses: \forall i <= k. /\ c_i */
  for (bucket = bconds_sel1->first; bucket; bucket = bucket->next)
  {
    cond = (BtorNode *) bucket->key;
    BTORLOG ("  cond: %s", node2string (cond));
    assert (BTOR_REAL_ADDR_NODE (cond)->len == 1);
    assert (!BTOR_REAL_ADDR_NODE (cond)->parameterized);
    add_new_exp_to_clause (btor, cond, -1, &linking_clause);
    btor_release_exp (btor, cond);
  }

  /* premisses bv conditions:
   *   false conditions: c_0, ..., c_l
   *   encode premisses: \forall i <= l. /\ \not c_i */
  for (bucket = bconds_sel2->first; bucket; bucket = bucket->next)
  {
    cond = (BtorNode *) bucket->key;
    BTORLOG ("  cond: %s", node2string (cond));
    assert (BTOR_REAL_ADDR_NODE (cond)->len == 1);
    assert (!BTOR_REAL_ADDR_NODE (cond)->parameterized);
    add_new_exp_to_clause (btor, cond, 1, &linking_clause);
    btor_release_exp (btor, cond);
  }

  /* add linking clause */
  while (!BTOR_EMPTY_STACK (linking_clause))
  {
    k = BTOR_POP_STACK (linking_clause);
    assert (k != 0);
    val = btor_fixed_sat (smgr, k);
    if (val < 0) continue;
    assert (!val);
    btor_add_sat (smgr, k);
    btor->stats.lclause_size_sum++;
  }
  btor_add_sat (smgr, 0);
  BTOR_RELEASE_STACK (mm, linking_clause);
}

#if 0
/* Encodes the following array inequality constraint:
* array1 != array2 <=> EXISTS(i): read(array1, i) != read(array2, i)
*/
static void
encode_array_inequality_virtual_reads (Btor * btor, BtorNode * aeq)
{
  assert (0);
  BtorNodePair *vreads;
  BtorNode *read1, *read2;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  BtorAIGVecMgr *avmgr;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  int len, k, d_k, r1_k, r2_k, e;
  BtorIntStack diffs;
  assert (btor);
  assert (aeq);
  assert (BTOR_IS_REGULAR_NODE (aeq));
  assert (BTOR_IS_ARRAY_EQ_NODE (aeq));
  assert (!aeq->tseitin);
  assert (aeq->vreads);
  mm = btor->mm;
  avmgr = btor->avmgr;
  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  vreads = aeq->vreads;

  read1 = vreads->exp1;
  assert (BTOR_IS_REGULAR_NODE (read1));
  assert (BTOR_IS_READ_NODE (read1));
  assert (BTOR_IS_SYNTH_NODE (read1));
  assert (!read1->tseitin);

  read2 = vreads->exp2;
  assert (BTOR_IS_REGULAR_NODE (read2));
  assert (BTOR_IS_READ_NODE (read2));
  assert (BTOR_IS_SYNTH_NODE (read2));
  assert (!read2->tseitin);

  assert (read1->e[1] == read2->e[1]);
  assert (BTOR_IS_REGULAR_NODE (read1->e[1]));
  assert (BTOR_IS_BV_VAR_NODE (read1->e[1]));
  assert (read1->len == read2->len);

  av1 = read1->av;
  assert (av1);
  av2 = read2->av;
  assert (av2);

  /* assign aig cnf indices as there are only variables,
   * no SAT constraints are generated */
  btor_aigvec_to_sat_tseitin (avmgr, aeq->av);
  aeq->tseitin = 1;
  btor_aigvec_to_sat_tseitin (avmgr, av1);
  read1->tseitin = 1;
  btor_aigvec_to_sat_tseitin (avmgr, av2);
  read2->tseitin = 1;

  /* encode !e => r1 != r2 */

  BTOR_INIT_STACK (diffs);
  len = read1->len;

  /* we do not need to hash the diffs as we never use
   * value1 != value2 in a lemma on demand */

  for (k = 0; k < len; k++)
    {
      aig1 = av1->aigs[k];
      assert (!BTOR_IS_INVERTED_AIG (aig1));
      assert (!BTOR_IS_CONST_AIG (aig1));
      assert (BTOR_IS_VAR_AIG (aig1));
      r1_k = aig1->cnf_id;
      assert (r1_k != 0);

      aig2 = av2->aigs[k];
      assert (!BTOR_IS_INVERTED_AIG (aig2));
      assert (!BTOR_IS_CONST_AIG (aig2));
      assert (BTOR_IS_VAR_AIG (aig2));
      r2_k = aig2->cnf_id;
      assert (r2_k != 0);

      d_k = btor_next_cnf_id_sat_mgr (smgr);
      BTOR_PUSH_STACK (mm, diffs, d_k);

      btor_add_sat (smgr, r1_k);
      btor_add_sat (smgr, r2_k);
      btor_add_sat (smgr, -d_k);
      btor_add_sat (smgr, 0);

      btor_add_sat (smgr, -r1_k);
      btor_add_sat (smgr, -r2_k);
      btor_add_sat (smgr, -d_k);
      btor_add_sat (smgr, 0);
    }

  assert (BTOR_IS_SYNTH_NODE (aeq));
  assert (aeq->av->len == 1);
  assert (!BTOR_IS_INVERTED_AIG (aeq->av->aigs[0]));
  assert (!BTOR_IS_CONST_AIG (aeq->av->aigs[0]));
  assert (BTOR_IS_VAR_AIG (aeq->av->aigs[0]));
  e = aeq->av->aigs[0]->cnf_id;
  assert (e != 0);

  assert (!BTOR_EMPTY_STACK (diffs));
  while (!BTOR_EMPTY_STACK (diffs))
    {
      d_k = BTOR_POP_STACK (diffs);
      btor_add_sat (smgr, d_k);
    }
  btor_add_sat (smgr, e);
  btor_add_sat (smgr, 0);
  BTOR_RELEASE_STACK (mm, diffs);
}
#endif

static void
add_lemma (Btor *btor, BtorNode *fun, BtorNode *app0, BtorNode *app1)
{
  assert (btor);
  assert (fun);
  assert (app0);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_FUN_NODE (fun));
  assert (!fun->parameterized);
  assert (BTOR_IS_REGULAR_NODE (app0));
  assert (BTOR_IS_APPLY_NODE (app0));
  assert (!app1 || BTOR_IS_REGULAR_NODE (app1));
  assert (!app1 || BTOR_IS_APPLY_NODE (app1));

  BtorPtrHashTable *bconds_sel1, *bconds_sel2;
  BtorNode *args, *value, *exp;
  BtorMemMgr *mm;

  mm = btor->mm;

  /* collect intermediate conditions of bit vector conditionals */
  bconds_sel1 = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  bconds_sel2 = btor_new_ptr_hash_table (mm,
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
      collect_premisses (btor, exp, fun, args, bconds_sel1, bconds_sel2);
    }
    encode_lemma (
        btor, bconds_sel1, bconds_sel2, app0, app1, app0->e[1], app1->e[1]);
  }
  /* beta reduction conflict */
  else
  {
    args = app0->e[1];
    btor_assign_args (btor, fun, args);
    value = btor_beta_reduce_partial (btor, fun, 0);  //&parameterized);
    btor_unassign_params (btor, fun);
    assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (value)));

    /* path from app0 to conflicting fun */
    collect_premisses (btor, app0, fun, args, bconds_sel1, bconds_sel2);

    /* path from conflicting fun to value */
    collect_premisses (
        btor, fun, BTOR_REAL_ADDR_NODE (value), args, bconds_sel1, bconds_sel2);

    encode_lemma (btor, bconds_sel1, bconds_sel2, app0, value, app0->e[1], 0);

    btor_release_exp (btor, value);
  }

  btor_delete_ptr_hash_table (bconds_sel1);
  btor_delete_ptr_hash_table (bconds_sel2);
}

static int
findfun_encode (BtorNode *exp)
{
  assert (exp);
  exp = BTOR_REAL_ADDR_NODE (exp);
  return !exp->tseitin
         && (BTOR_IS_APPLY_NODE (exp) || BTOR_IS_BV_VAR_NODE (exp));
}

static int
propagate (Btor *btor,
           BtorNodePtrStack *prop_stack,
           BtorNodePtrStack *cleanup_stack,
           int *assignments_changed)
{
  assert (btor);
  assert (prop_stack);
  assert (cleanup_stack);
  // TODO: extensionality for write lambdas
  assert (btor->ops[BTOR_AEQ_NODE] == 0);
  assert (btor->ops[BTOR_READ_NODE] == 0);
  assert (btor->ops[BTOR_ACOND_NODE] == 0);
  assert (btor->ops[BTOR_WRITE_NODE] == 0);

  int i, values_equal, args_equal;
  char *fun_value_assignment, *app_assignment;
  BtorMemMgr *mm;
  BtorLambdaNode *lambda;
  BtorNode *fun, *app, *args, *fun_value, *parameterized, *param_app;
  BtorNode *hashed_app;
  BtorPtrHashBucket *b;
  BtorNodePtrStack param_apps;

  BTOR_INIT_STACK (param_apps);

  mm = btor->mm;

  BTORLOG ("");
  BTORLOG ("*** %s", __FUNCTION__);
  while (!BTOR_EMPTY_STACK (*prop_stack))
  {
    btor->stats.propagations++;
    fun = BTOR_POP_STACK (*prop_stack);
    assert (BTOR_IS_REGULAR_NODE (fun));
    assert (BTOR_IS_FUN_NODE (fun));
    assert (!fun->simplified);
    assert (!BTOR_EMPTY_STACK (*prop_stack));
    app = BTOR_POP_STACK (*prop_stack);
    assert (BTOR_IS_REGULAR_NODE (app));
    assert (BTOR_IS_APPLY_NODE (app));
    assert (app->refs - app->ext_refs > 0);
    check_not_simplified_or_const (btor, app);

    BTORLOG ("propagate");
    BTORLOG ("  app: %s", node2string (app));
    BTORLOG ("  fun: %s", node2string (fun));

    *assignments_changed = lazy_synthesize_and_encode_apply_exp (btor, app, 1);

    if (*assignments_changed) return 0;

    args = app->e[1];
    assert (BTOR_IS_REGULAR_NODE (args));
    assert (BTOR_IS_ARGS_NODE (args));
    check_not_simplified_or_const (btor, app);
    check_not_simplified_or_const (btor, args);

    if (!fun->rho)
    {
      fun->rho =
          btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) hash_assignment,
                                   (BtorCmpPtr) compare_argument_assignments);
      BTOR_PUSH_STACK (mm, *cleanup_stack, fun);
    }
    else
    {
      b = btor_find_in_ptr_hash_table (fun->rho, args);
      if (b)
      {
        hashed_app = (BtorNode *) b->data.asPtr;
        assert (BTOR_IS_REGULAR_NODE (hashed_app));
        assert (BTOR_IS_APPLY_NODE (hashed_app));

        if (compare_assignments (hashed_app, app) != 0)
        {
          BTORLOG ("\e[1;31m");
          BTORLOG ("A1 conflict at: %s", node2string (fun));
          BTORLOG ("add_lemma:");
          BTORLOG ("  fun: %s", node2string (fun));
          BTORLOG ("  app1: %s", node2string (hashed_app));
          BTORLOG ("  app2: %s", node2string (app));
          BTORLOG ("\e[0;39m");
          btor->stats.array_axiom_1_conflicts++;
          add_lemma (btor, fun, hashed_app, app);
          return 1;
        }
        else
          continue;
      }
    }
    assert (fun->rho);
    assert (!btor_find_in_ptr_hash_table (fun->rho, args));
    btor_insert_in_ptr_hash_table (fun->rho, args)->data.asPtr = app;
    BTORLOG ("  save app: %s (%s)", node2string (args), node2string (app));

    /* skip array vars */
    if (!BTOR_IS_LAMBDA_NODE (fun))
    {
      assert (BTOR_IS_ARRAY_VAR_NODE (fun));
      continue;
    }

    lambda = (BtorLambdaNode *) fun;

    *assignments_changed = lazy_synthesize_and_encode_lambda_exp (btor, fun, 1);
    if (*assignments_changed) return 0;

    btor_assign_args (btor, fun, args);
    fun_value = btor_beta_reduce_partial (btor, fun, &parameterized);
    assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (fun_value)));
    //      // debug
    //      char *b = btor_eval_exp (btor, fun_value);
    //      BTORLOG ("  fun_value: %s, %s", b, node2string (fun_value));
    //      btor_freestr (btor->mm, b);
    //      // debug

    if (BTOR_IS_ARRAY_VAR_NODE (BTOR_REAL_ADDR_NODE (fun_value)))
    {
      BTOR_PUSH_STACK (mm, *prop_stack, app);
      BTOR_PUSH_STACK (mm, *prop_stack, fun_value);
      btor_unassign_params (btor, fun);
      btor_release_exp (btor, fun_value);
      continue;
    }

    if (parameterized)
    {
      assert (BTOR_IS_REGULAR_NODE (parameterized));
      //	  assert (!BTOR_IS_APPLY_NODE (parameterized)
      //	          || BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE
      //(fun_value)));

      BTOR_INIT_STACK (param_apps);

      args_equal = 0;
      if (BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (fun_value))
          && ENABLE_APPLY_PROP_DOWN)
        args_equal = BTOR_REAL_ADDR_NODE (fun_value)->e[1] == args;

      if (!args_equal)
      {
        find_nodes_dfs (
            btor, fun_value, &param_apps, findfun_encode, skipfun_tseitin);

        if (!BTOR_EMPTY_STACK (param_apps))
        {
          if (!lambda->synth_apps)
          {
            lambda->synth_apps =
                btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
          }

          for (i = 0; i < BTOR_COUNT_STACK (param_apps); i++)
          {
            param_app = param_apps.start[i];
            assert (BTOR_IS_REGULAR_NODE (param_app));
            //		      assert (BTOR_IS_APPLY_NODE (param_app));
            assert (BTOR_IS_APPLY_NODE (param_app)
                    || BTOR_IS_BV_VAR_NODE (param_app));

            if (param_app->tseitin) continue;

            if (BTOR_IS_BV_VAR_NODE (param_app))
            {
              *assignments_changed =
                  lazy_synthesize_and_encode_var_exp (btor, param_app, 1);
            }
            else
            {
              assert (BTOR_IS_APPLY_NODE (param_app));

              if (btor_find_in_ptr_hash_table (lambda->synth_apps, param_app))
                continue;

              btor_insert_in_ptr_hash_table (lambda->synth_apps,
                                             btor_copy_exp (btor, param_app));

              btor->stats.lambda_synth_apps++;
              *assignments_changed =
                  lazy_synthesize_and_encode_apply_exp (btor, param_app, 1);
            }

            if (*assignments_changed)
            {
              btor_unassign_params (btor, fun);
              btor_release_exp (btor, fun_value);
              BTOR_RELEASE_STACK (mm, param_apps);
              return 0;
            }
          }
        }
      }

      /* NOTE: this is a special case
       * 'fun_value' is a function application and is not encoded.
       * the value of 'fun_value' must be the same as 'app'.
       * if 'fun_value' and 'app' have the same number of arguments and
       * the arguments have the same value, we can propagate 'app'
       * instead of 'fun_value'. in this case, we do not have to
       * additionally encode 'fun_value', but we can use 'app' instead,
       * which has the same properties as 'fun_value'. further, we do not
       * have to encode every intermediate function application we
       * encounter while propagating 'app'. */
      if (BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (fun_value))
          //	      && BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE
          //(parameterized))
          && args_equal)
      {
        //	      assert (
        //		BTOR_REAL_ADDR_NODE (fun_value)->e[0] ==
        // parameterized->e[0]); 	      assert (BTOR_IS_APPLY_NODE
        //(parameterized));
        BTOR_PUSH_STACK (mm, *prop_stack, app);
        //	      BTOR_PUSH_STACK (mm, *prop_stack, parameterized->e[0]);
        BTOR_PUSH_STACK (
            mm, *prop_stack, BTOR_REAL_ADDR_NODE (fun_value)->e[0]);
        BTORLOG ("  propagate down: %s", node2string (app));
        //	      BTORLOG ("    parameterized: %s (%s)",
        //		       node2string (parameterized),
        //		       node2string (parameterized->e[1]));
        //	      BTORLOG ("    value: %s (%s)", node2string (fun_value),
        //		       node2string (BTOR_REAL_ADDR_NODE
        //(fun_value)->e[1]));
        btor->stats.propagations_down++;
      }
      else
      {
        /* compute assignment of 'fun_value' and compare it to the
         * assignment of 'app'. */
        app_assignment = btor_bv_assignment_exp (btor, app);
        //	      if (BTOR_REAL_ADDR_NODE (fun_value)->tseitin
        //		  || BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE
        //(fun_value)))
        fun_value_assignment = btor_eval_exp (btor, fun_value);
        //	      else
        //		fun_value_assignment =
        //		  btor_eval_exp (btor, BTOR_LAMBDA_GET_BODY (fun));
        assert (fun_value_assignment);
        values_equal = strcmp (app_assignment, fun_value_assignment) == 0;
        btor_freestr (mm, fun_value_assignment);
        btor_free_bv_assignment_exp (btor, app_assignment);

        if (!values_equal)
        {
        LAMBDA_AXIOM_2_CONFLICT:
          BTORLOG ("\e[1;31m");
          BTORLOG ("A2 conflict at: %s", node2string (fun));
          BTORLOG ("add_lemma:");
          BTORLOG ("  fun: %s", node2string (fun));
          BTORLOG ("  app: %s", node2string (app));
          BTORLOG ("\e[0;39m");
          btor->stats.array_axiom_2_conflicts++;
          add_lemma (btor, fun, app, 0);
          btor_unassign_params (btor, fun);
          btor_release_exp (btor, fun_value);
          if (parameterized) BTOR_RELEASE_STACK (mm, param_apps);
          return 1;
        }
        else if (!BTOR_EMPTY_STACK (param_apps))
        {
          /* in case that we did not encounter any conflict, but
           * instantiated and encoded function applications, we need
           * to propagate them. */
          for (i = 0; i < BTOR_COUNT_STACK (param_apps); i++)
          {
            param_app = BTOR_REAL_ADDR_NODE (param_apps.start[i]);
            assert (BTOR_IS_REGULAR_NODE (param_app));
            assert (BTOR_IS_APPLY_NODE (param_app)
                    || BTOR_IS_BV_VAR_NODE (param_app));

            if (!BTOR_IS_APPLY_NODE (param_app)) continue;

            BTOR_PUSH_STACK (mm, *prop_stack, param_app);
            BTOR_PUSH_STACK (mm, *prop_stack, param_app->e[0]);
          }
        }
      }
      BTOR_RELEASE_STACK (mm, param_apps);
    }
    else
    {
      /* we already have an assignment for 'fun_value' and we can check
       * if both function value 'app' and 'fun_value' are the same */
      if (compare_assignments (app, fun_value) != 0)
        goto LAMBDA_AXIOM_2_CONFLICT;
    }
    btor_unassign_params (btor, fun);
    btor_release_exp (btor, fun_value);
  }

  return 0;
}

static int
check_and_resolve_conflicts (Btor *btor, BtorNodePtrStack *top_functions)
{
  assert (btor);
  assert (top_functions);
  assert (btor->ops[BTOR_AEQ_NODE] == 0);

  int found_conflict, changed_assignments;
  BtorMemMgr *mm;
  BtorNode *cur_fun, *cur_parent, **top, **temp, *param_app;
  BtorNodePtrStack fun_stack, cleanup_stack, working_stack, unmark_stack;
  BtorNodePtrStack param_apps;
  BtorPartialParentIterator it;

  found_conflict = 0;
  mm             = btor->mm;
BTOR_CONFLICT_CHECK:
  assert (!found_conflict);
  changed_assignments = 0;
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (working_stack);
  BTOR_INIT_STACK (cleanup_stack);
  BTOR_INIT_STACK (fun_stack);
  BTOR_INIT_STACK (param_apps);

  /* push all top arrays on the stack */
  top = top_functions->top;
  for (temp = top_functions->start; temp != top; temp++)
  {
    cur_fun = *temp;
    assert (BTOR_IS_REGULAR_NODE (cur_fun));
    assert (BTOR_IS_FUN_NODE (cur_fun));
    assert (cur_fun->reachable);
    assert (!cur_fun->simplified);
    BTOR_PUSH_STACK (mm, fun_stack, cur_fun);
  }

  while (!BTOR_EMPTY_STACK (fun_stack))
  {
    cur_fun = BTOR_POP_STACK (fun_stack);
    assert (BTOR_IS_REGULAR_NODE (cur_fun));
    assert (BTOR_IS_FUN_NODE (cur_fun));
    assert (cur_fun->reachable);
    assert (!cur_fun->simplified);
    assert (cur_fun->fun_mark == 0 || cur_fun->fun_mark == 1);

    if (cur_fun->fun_mark == 0)
    {
      cur_fun->fun_mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, cur_fun);
      assert (BTOR_IS_FUN_NODE (cur_fun));

      /* push all underlying functions on fun_stack that are accessed
       * via parameterized apply nodes */
      if (BTOR_IS_LAMBDA_NODE (cur_fun))
      {
        assert (BTOR_IS_PARAM_NODE (cur_fun->e[0]));
        assert (BTOR_EMPTY_STACK (param_apps));
        find_nodes_dfs (
            btor, cur_fun->e[1], &param_apps, findfun_param_apply, 0);

        while (!BTOR_EMPTY_STACK (param_apps))
        {
          param_app = BTOR_POP_STACK (param_apps);
          assert (BTOR_IS_REGULAR_NODE (param_app));
          assert (BTOR_IS_APPLY_NODE (param_app));
          BTOR_PUSH_STACK (mm, fun_stack, param_app->e[0]);
        }
        BTOR_RESET_STACK (param_apps);
      }

      /* check consistency for non-parameterized apply nodes */
      init_apply_parent_iterator (&it, cur_fun);
      while (has_next_parent_apply_parent_iterator (&it))
      {
        cur_parent = next_parent_apply_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (cur_parent));
        assert (BTOR_IS_APPLY_NODE (cur_parent));

        /* skip parameterized applications */
        if (cur_parent->parameterized) continue;

        /* we only process reachable or virtual applications */
        check_not_simplified_or_const (btor, cur_parent);
        if (cur_parent->reachable || cur_parent->vread)
        {
          /* push read-array pair on working stack */
          BTOR_PUSH_STACK (mm, working_stack, cur_parent);
          BTOR_PUSH_STACK (mm, working_stack, cur_fun);
          found_conflict = propagate (
              btor, &working_stack, &cleanup_stack, &changed_assignments);
          if (found_conflict || changed_assignments) goto BTOR_CONFLICT_CLEANUP;
        }
      }
    }
  }
BTOR_CONFLICT_CLEANUP:
  while (!BTOR_EMPTY_STACK (cleanup_stack))
  {
    cur_fun = BTOR_POP_STACK (cleanup_stack);
    assert (BTOR_IS_REGULAR_NODE (cur_fun));
    assert (BTOR_IS_FUN_NODE (cur_fun));
    assert (cur_fun->rho);

    if (found_conflict || changed_assignments)
    {
      btor_delete_ptr_hash_table (cur_fun->rho);
      cur_fun->rho = 0;
    }
    else
    {
      /* remember arrays for incremental usage (and prevent premature
       * release in case that array is released via API call) */
      BTOR_PUSH_STACK (
          mm, btor->arrays_with_model, btor_copy_exp (btor, cur_fun));
    }
  }
  BTOR_RELEASE_STACK (mm, cleanup_stack);
  BTOR_RELEASE_STACK (mm, working_stack);
  BTOR_RELEASE_STACK (mm, fun_stack);
  BTOR_RELEASE_STACK (mm, param_apps);

  /* reset array marks of arrays */
  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur_fun = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur_fun));
    assert (BTOR_IS_FUN_NODE (cur_fun));
    assert (cur_fun->fun_mark == 1);
    cur_fun->fun_mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);

  /* restart? (assignments changed during lazy synthesis and encoding) */
  if (changed_assignments)
  {
    btor->stats.synthesis_assignment_inconsistencies++;
    BTORLOG ("synthesis assignment inconsistency: %d",
             btor->stats.synthesis_assignment_inconsistencies);
    goto BTOR_CONFLICT_CHECK;
  }
  return found_conflict;
}

static int
btor_sat_aux_btor (Btor *btor)
{
  int sat_result, found_conflict, found_constraint_false, verbosity;
  int found_assumption_false, refinements;
  BtorNodePtrStack top_functions;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorMemMgr *mm;

  assert (btor);
  verbosity = btor->verbosity;

  if (btor->inconsistent) return BTOR_UNSAT;

  btor_msg (btor, 1, "calling SAT");

  // TODO: use return value?
  btor_simplify (btor);

  if (btor->inconsistent) return BTOR_UNSAT;

  mm = btor->mm;

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  if (!btor_is_initialized_sat (smgr)) btor_init_sat (smgr);

  if (btor->valid_assignments == 1) btor_reset_incremental_usage (btor);

  BTOR_ABORT_CORE (btor->ops[BTOR_AEQ_NODE] > 0,
                   "extensionality on arrays/lambdas not yet supported");

  do
  {
    assert (check_all_hash_tables_proxy_free_dbg (btor));
    assert (check_all_hash_tables_simp_free_dbg (btor));
    found_constraint_false = process_unsynthesized_constraints (btor);
    assert (check_all_hash_tables_proxy_free_dbg (btor));
    assert (check_all_hash_tables_simp_free_dbg (btor));

    if (found_constraint_false)
    {
    UNSAT:
      sat_result = BTOR_UNSAT;
      goto DONE;
    }
  } while (btor->unsynthesized_constraints->count > 0);

  update_reachable (btor);

  if (btor->model_gen)
  {
    synthesize_all_var_rhs (btor);
    synthesize_all_array_rhs (btor);
    if (btor->generate_model_for_all_reads) synthesize_all_reads (btor);
  }

  update_assumptions (btor);

  found_assumption_false = add_again_assumptions (btor);
  if (found_assumption_false) goto UNSAT;

  BTOR_INIT_STACK (top_functions);
  sat_result = btor_timed_sat_sat (btor, -1);

  while (sat_result == BTOR_SAT)
  {
    assert (BTOR_EMPTY_STACK (top_functions));
    search_top_functions (btor, &top_functions);

    found_conflict = check_and_resolve_conflicts (btor, &top_functions);

    if (found_conflict)
    {
      btor->stats.lod_refinements++;
      found_assumption_false = add_again_assumptions (btor);
      assert (!found_assumption_false);
    }

    BTOR_RELEASE_STACK (mm, top_functions);

    if (!found_conflict) break;

    if (verbosity > 1)
    {
      refinements = btor->stats.lod_refinements;
      if (verbosity > 2 || !(refinements % 10))
      {
        fprintf (stdout, "[btorsat] refinement iteration %d\n", refinements);
        fflush (stdout);
      }
    }

    found_assumption_false = add_again_assumptions (btor);
    if (found_assumption_false)
      sat_result = BTOR_UNSAT;
    else
      sat_result = btor_timed_sat_sat (btor, -1);
  }

DONE:

  btor->valid_assignments = 1;
  BTOR_ABORT_CORE (sat_result != BTOR_SAT && sat_result != BTOR_UNSAT,
                   "result must be sat or unsat");

  btor->last_sat_result = sat_result;
  return sat_result;
}

int
btor_sat_btor (Btor *btor)
{
  int res;
  assert (btor);
  assert (btor->btor_sat_btor_called >= 0);
  assert (btor->inc_enabled || btor->btor_sat_btor_called == 0);
  res = btor_sat_aux_btor (btor);
  btor->btor_sat_btor_called++;
  return res;
}

int
btor_fun_sort_check (Btor *btor, int argc, BtorNode **args, BtorNode *fun)
{
  (void) btor;
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_LAMBDA_NODE (fun));
  assert (argc == btor_get_lambda_arity (btor, fun));

  int i;
  BtorNode *arg;
  BtorParamNode *param;
  BtorIterator it;

  init_lambda_iterator (&it, fun);

  for (i = 0; i < argc; i++)
  {
    assert (has_next_lambda_iterator (&it));
    arg   = BTOR_REAL_ADDR_NODE (args[i]);
    param = BTOR_LAMBDA_GET_PARAM (next_lambda_iterator (&it));
    assert (BTOR_IS_REGULAR_NODE (param));

    if (arg->len != param->len) return i;
  }
  return -1;
}

#if 0
static BtorNode *
vread_index_exp (Btor * btor, int len)
{
  char *symbol;
  size_t bytes;
  BtorNode *result;
  assert (btor);
  assert (len > 0);
  BTOR_ABORT_NODE (btor->vread_index_id == INT_MAX, "vread index id overflow");
  bytes = 6 + btor_num_digits_util (btor->vread_index_id) + 1;
  bytes *= sizeof (char);
  symbol = (char *) btor_malloc (btor->mm, bytes);
  sprintf (symbol, "vindex%d", btor->vread_index_id);
  btor->vread_index_id++;
  result = btor_var_exp (btor, len, symbol);
  btor_free (btor->mm, symbol, bytes);
  return result;
}
#endif

#if 0
static void
synthesize_array_equality (Btor * btor, BtorNode * aeq)
{
  BtorNode *index, *read1, *read2;
  BtorAIGVecMgr *avmgr;
  assert (btor);
  assert (aeq);
  assert (BTOR_IS_REGULAR_NODE (aeq));
  assert (BTOR_IS_ARRAY_EQ_NODE (aeq));
  assert (!BTOR_IS_SYNTH_NODE (aeq));
  avmgr = btor->avmgr;
  aeq->av = btor_var_aigvec (avmgr, 1);
  /* generate virtual reads */
  index = vread_index_exp (btor, aeq->e[0]->index_len);
  index->vread_index = 1;

  /* we do not want optimizations for the virtual reads
   * and the equality, e.g. rewriting of reads on array
   * conditionals, so we call 'btor_read_exp_node' directly.
   */
  read1 = btor_read_exp_node (btor, aeq->e[0], index);
  read2 = btor_read_exp_node (btor, aeq->e[1], index);

  /* mark them as virtual */
  read1->vread = 1;
  read2->vread = 1;

  aeq->vreads = new_exp_pair (btor, read1, read2);

  read1->av = btor_var_aigvec (avmgr, read1->len);
  btor->stats.vreads++;
  if (read1 != read2)
    {
      read2->av = btor_var_aigvec (avmgr, read2->len);
      btor->stats.vreads++;
    }

  encode_array_inequality_virtual_reads (btor, aeq);

  btor_release_exp (btor, index);
  btor_release_exp (btor, read1);
  btor_release_exp (btor, read2);
}
#endif

BtorAIG *
btor_exp_to_aig (Btor *btor, BtorNode *exp)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorAIGVec *av;
  BtorAIG *result;

  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);

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

#if 1
char *
btor_eval_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int i;
  char *res = 0;
  double start;
  BtorMemMgr *mm;
  BtorNodePtrStack work_stack;
  BtorVoidPtrStack arg_stack;
  BtorNode *cur, *real_cur, *next;
  BtorPtrHashTable *cache;
  BtorPtrHashBucket *b;
  BitVector *result = 0, *inv_result, **e;

  // TODO: return if tseitin
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  mm    = btor->mm;
  start = btor_time_stamp ();
  btor->stats.eval_exp_calls++;

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

    /* if we do not have an assignment for an apply we cannot compute the
     * corresponding value */
    if (BTOR_IS_APPLY_NODE (real_cur) && !real_cur->tseitin)
    {
      result = 0;
      goto EVAL_EXP_CLEANUP_EXIT;
    }
    else if (BTOR_IS_BV_VAR_NODE (real_cur) && !real_cur->tseitin)
    {
      result = 0;
      goto EVAL_EXP_CLEANUP_EXIT;
    }

    if (real_cur->eval_mark == 0)
    {
      if (real_cur->tseitin)
      {
        assert (BTOR_IS_SYNTH_NODE (real_cur));
        result = btor_assignment_bv (btor, real_cur);
        goto EVAL_EXP_PUSH_RESULT;
      }
      else if (BTOR_IS_BV_CONST_NODE (real_cur))
      {
        result = btor_char_to_bv (btor, real_cur->bits);
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
      e = (BitVector **) arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result = btor_slice_bv (btor, e[0], real_cur->upper, real_cur->lower);
          btor_free_bv (btor, e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_BEQ_NODE:
          result = btor_eq_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_BCOND_NODE:
          if (btor_is_true_bv (e[2]))
            result = btor_copy_bv (btor, e[1]);
          else
            result = btor_copy_bv (btor, e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          btor_free_bv (btor, e[2]);
          break;
        default:
          BTORLOG ("  *** %s", node2string (real_cur));
          /* should be unreachable */
          assert (0);
      }

      assert (!btor_find_in_ptr_hash_table (cache, real_cur));
      btor_insert_in_ptr_hash_table (cache, real_cur)->data.asPtr =
          btor_copy_bv (btor, result);

    EVAL_EXP_PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_bv (btor, result);
        btor_free_bv (btor, result);
        result = inv_result;
      }

      BTOR_PUSH_STACK (mm, arg_stack, result);
    }
    else
    {
      assert (real_cur->eval_mark == 2);
      b = btor_find_in_ptr_hash_table (cache, real_cur);
      assert (b);
      result = btor_copy_bv (btor, (BitVector *) b->data.asPtr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

EVAL_EXP_CLEANUP_EXIT:
  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur            = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));
    cur->eval_mark = 0;
  }

  while (!BTOR_EMPTY_STACK (arg_stack))
  {
    inv_result = BTOR_POP_STACK (arg_stack);
    btor_free_bv (btor, inv_result);
  }

  for (b = cache->first; b; b = b->next)
  {
    real_cur            = (BtorNode *) b->key;
    real_cur->eval_mark = 0;
    btor_free_bv (btor, (BitVector *) b->data.asPtr);
  }

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  btor_delete_ptr_hash_table (cache);

  //  BTORLOG ("%s: %s '%s'", __FUNCTION__, node2string (exp), result);
  btor->time.eval += btor_time_stamp () - start;

  if (result)
  {
    res = btor_bv_to_char_bv (btor, result);
    btor_free_bv (btor, result);
  }

  return res;
}
#else
char *
btor_eval_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int i;
  char *result = 0, *inv_result;
  char **e;
  double start;
  BtorMemMgr *mm;
  BtorNodePtrStack work_stack;
  BtorCharPtrStack arg_stack;
  BtorNode *cur, *real_cur, *next;
  BtorPtrHashTable *cache;
  BtorPtrHashBucket *b;

  // TODO: return if tseitin
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  mm = btor->mm;
  start = btor_time_stamp ();
  btor->stats.eval_exp_calls++;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (arg_stack);
  cache = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_PUSH_STACK (mm, work_stack, exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->eval_mark);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_POP_STACK (work_stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!real_cur->simplified);

    /* if we do not have an assignment for an apply we cannot compute the
     * corresponding value */
    if (BTOR_IS_APPLY_NODE (real_cur) && !real_cur->tseitin)
    {
      result = 0;
      goto EVAL_EXP_CLEANUP_EXIT;
    }
    else if (BTOR_IS_BV_VAR_NODE (real_cur) && !real_cur->tseitin)
    {
      result = 0;
      goto EVAL_EXP_CLEANUP_EXIT;
    }

    if (real_cur->eval_mark == 0)
    {
      if (real_cur->tseitin)
      {
        assert (BTOR_IS_SYNTH_NODE (real_cur));
        result = btor_assignment_aigvec (btor->avmgr, real_cur->av);
        goto EVAL_EXP_PUSH_RESULT;
      }
      else if (BTOR_IS_BV_CONST_NODE (real_cur))
      {
        result = btor_copy_const (mm, real_cur->bits);
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
      //	  BTOR_PUSH_STACK (mm, unmark_stack, real_cur);
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
      e = arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result =
              btor_slice_const (mm, e[0], real_cur->upper, real_cur->lower);
          btor_freestr (mm, (char *) e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_BEQ_NODE:
          result = btor_eq_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_const (mm, e[1], e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          break;
        case BTOR_BCOND_NODE:
          if (e[2][0] == '1')
            result = btor_copy_const (mm, e[1]);
          else
            result = btor_copy_const (mm, e[0]);
          btor_freestr (mm, (char *) e[0]);
          btor_freestr (mm, (char *) e[1]);
          btor_freestr (mm, (char *) e[2]);
          break;
        default:
          BTORLOG ("  *** %s", node2string (real_cur));
          /* should be unreachable */
          assert (0);
      }

      assert (!btor_find_in_ptr_hash_table (cache, real_cur));
      btor_insert_in_ptr_hash_table (cache, real_cur)->data.asStr =
          btor_copy_const (mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_const (mm, result);
        btor_freestr (mm, (char *) result);
        result = inv_result;
      }

      BTOR_PUSH_STACK (mm, arg_stack, (char *) result);
    }
    else
    {
      assert (real_cur->eval_mark == 2);
      b = btor_find_in_ptr_hash_table (cache, real_cur);
      assert (b);
      result = btor_copy_const (mm, b->data.asStr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

EVAL_EXP_CLEANUP_EXIT:
  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));
    cur->eval_mark = 0;
  }

  while (!BTOR_EMPTY_STACK (arg_stack))
  {
    inv_result = BTOR_POP_STACK (arg_stack);
    btor_freestr (mm, (char *) inv_result);
  }

  for (b = cache->first; b; b = b->next)
  {
    real_cur = (BtorNode *) b->key;
    real_cur->eval_mark = 0;
    btor_freestr (mm, b->data.asStr);
  }

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  btor_delete_ptr_hash_table (cache);

  //  BTORLOG ("%s: %s '%s'", __FUNCTION__, node2string (exp), result);
  btor->time.eval += btor_time_stamp () - start;
  return result;
}
#endif

char *
btor_bv_assignment_exp (Btor *btor, BtorNode *exp)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGVec *av;
  BtorNode *real_exp;
  char *assignment;
  int invert_av, invert_bits;

  assert (btor);
  assert (!btor->inconsistent);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (real_exp);

  if (BTOR_IS_BV_CONST_NODE (real_exp))
  {
    invert_bits = BTOR_IS_INVERTED_NODE (exp);
    if (invert_bits)
      btor_invert_const (btor->mm, BTOR_REAL_ADDR_NODE (exp)->bits);
    assignment = btor_copy_const (btor->mm, BTOR_REAL_ADDR_NODE (exp)->bits);
    if (invert_bits)
      btor_invert_const (btor->mm, BTOR_REAL_ADDR_NODE (exp)->bits);
  }
  else if (!real_exp->vread
           && (!real_exp->reachable || !BTOR_IS_SYNTH_NODE (real_exp)))
  {
    assignment = btor_x_const_3vl (btor->mm, real_exp->len);
  }
  else
  {
    avmgr     = btor->avmgr;
    invert_av = BTOR_IS_INVERTED_NODE (exp);
    av        = BTOR_REAL_ADDR_NODE (exp)->av;
    if (invert_av) btor_invert_aigvec (avmgr, av);
    assignment = btor_assignment_aigvec (avmgr, av);
    /* invert back if necessary */
    if (invert_av) btor_invert_aigvec (avmgr, av);
  }

  return assignment;
}

void
btor_array_assignment_exp (
    Btor *btor, BtorNode *exp, char ***indices, char ***values, int *size)
{
  BtorPtrHashBucket *b;
  BtorNode *index, *value, *args;
  int i;

  assert (btor);
  assert (!btor->inconsistent);
  assert (exp);
  assert (!BTOR_IS_INVERTED_NODE (exp));
  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_IS_ARRAY_NODE (exp));
  assert (indices);
  assert (values);
  assert (size);

  i = 0;

  if (!exp->rho)
  {
    *size = 0;
    return;
  }

  *size = (int) exp->rho->count;
  if (*size > 0)
  {
    BTOR_NEWN (btor->mm, *indices, *size);
    BTOR_NEWN (btor->mm, *values, *size);

    for (b = exp->rho->first; b; b = b->next)
    {
      args = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (args));
      assert (BTOR_IS_ARGS_NODE (args));
      assert (args->arity == 1);
      index         = args->e[0];
      value         = BTOR_GET_VALUE_ACC_NODE ((BtorNode *) b->data.asPtr);
      (*indices)[i] = btor_bv_assignment_exp (btor, index);
      (*values)[i]  = btor_bv_assignment_exp (btor, value);
      i++;
    }
  }
}

void
btor_free_bv_assignment_exp (Btor *btor, char *assignment)
{
  assert (btor);
  assert (assignment);
  btor_freestr (btor->mm, assignment);
}

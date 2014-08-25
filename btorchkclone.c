/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "btorchkclone.h"
#include "btorbitvec.h"
#include "btorcore.h"
#include "btoriter.h"
#include "btoropt.h"

static void
btor_chkclone_mem (Btor *btor)
{
  assert (btor);
  assert (btor->clone);
  assert (btor->mm);
  assert (btor->clone->mm);
  assert (btor->mm->allocated
              - (btor->msg_prefix
                     ? (strlen (btor->msg_prefix) + 1) * sizeof (char)
                     : 0)
          == btor->clone->mm->allocated
                 - (btor->clone->msg_prefix
                        ? (strlen (btor->clone->msg_prefix) + 1) * sizeof (char)
                        : 0));
  assert (btor->mm->sat_allocated == btor->clone->mm->sat_allocated);
  /* Note: both maxallocated and sat_maxallocated may differ! */
}

#define BTOR_CHKCLONE_STATE(field)        \
  do                                      \
  {                                       \
    assert (clone->field == btor->field); \
  } while (0)

static void
btor_chkclone_state (Btor *btor)
{
  assert (btor);

  Btor *clone;

  clone = btor->clone;
  assert (clone);

  BTOR_CHKCLONE_STATE (dvn_id);
  BTOR_CHKCLONE_STATE (dan_id);
  BTOR_CHKCLONE_STATE (dpn_id);
  BTOR_CHKCLONE_STATE (dfn_id);
  BTOR_CHKCLONE_STATE (rec_rw_calls);
  BTOR_CHKCLONE_STATE (rec_read_acond_calls);
  BTOR_CHKCLONE_STATE (valid_assignments);
  BTOR_CHKCLONE_STATE (vis_idx);
  BTOR_CHKCLONE_STATE (vread_index_id);
  BTOR_CHKCLONE_STATE (inconsistent);
  BTOR_CHKCLONE_STATE (found_constraint_false);
  BTOR_CHKCLONE_STATE (external_refs);
  BTOR_CHKCLONE_STATE (btor_sat_btor_called);
  BTOR_CHKCLONE_STATE (last_sat_result);
}

#define BTOR_CHKCLONE_STATS(field)                    \
  do                                                  \
  {                                                   \
    assert (clone->stats.field == btor->stats.field); \
  } while (0)

#define BTOR_CHKCLONE_CONSTRAINTSTATS(constraints, field)                     \
  do                                                                          \
  {                                                                           \
    assert (clone->stats.constraints.field == btor->stats.constraints.field); \
  } while (0)

static void
btor_chkclone_stats (Btor *btor)
{
  assert (btor);

  Btor *clone;

  clone = btor->clone;
  assert (clone);

  BTOR_CHKCLONE_STATS (max_rec_rw_calls);
  BTOR_CHKCLONE_STATS (lod_refinements);
  BTOR_CHKCLONE_STATS (synthesis_assignment_inconsistencies);
  BTOR_CHKCLONE_STATS (synthesis_inconsistency_apply);
  BTOR_CHKCLONE_STATS (synthesis_inconsistency_lambda);
  BTOR_CHKCLONE_STATS (function_congruence_conflicts);
  BTOR_CHKCLONE_STATS (beta_reduction_conflicts);
  BTOR_CHKCLONE_STATS (var_substitutions);
  BTOR_CHKCLONE_STATS (array_substitutions);
  BTOR_CHKCLONE_STATS (ec_substitutions);
  BTOR_CHKCLONE_STATS (vreads);
  BTOR_CHKCLONE_STATS (linear_equations);
  BTOR_CHKCLONE_STATS (gaussian_eliminations);
  BTOR_CHKCLONE_STATS (eliminated_slices);
  BTOR_CHKCLONE_STATS (skeleton_constraints);
  BTOR_CHKCLONE_STATS (adds_normalized);
  BTOR_CHKCLONE_STATS (ands_normalized);
  BTOR_CHKCLONE_STATS (muls_normalized);
  BTOR_CHKCLONE_STATS (read_props_construct);
  BTOR_CHKCLONE_STATS (lemmas_size_sum);
  BTOR_CHKCLONE_STATS (lclause_size_sum);

  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, varsubst);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, embedded);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, unsynthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, synthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, varsubst);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, embedded);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, unsynthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, synthesized);

  BTOR_CHKCLONE_STATS (expressions);
  BTOR_CHKCLONE_STATS (beta_reduce_calls);
  BTOR_CHKCLONE_STATS (eval_exp_calls);
  BTOR_CHKCLONE_STATS (lambda_synth_apps);
  BTOR_CHKCLONE_STATS (lambdas_merged);
  BTOR_CHKCLONE_STATS (propagations);
  BTOR_CHKCLONE_STATS (propagations_down);
  BTOR_CHKCLONE_STATS (apply_props_construct);
}

#define BTOR_CHKCLONE_OPT(field)                                          \
  do                                                                      \
  {                                                                       \
    BTOR_CHKCLONE_STATE (options.field.internal);                         \
    assert ((!btor->options.field.shrt && !clone->options.field.shrt)     \
            || (btor->options.field.shrt                                  \
                && !strcmp (clone->options.field.shrt,                    \
                            btor->options.field.shrt)));                  \
    assert (!strcmp (clone->options.field.lng, btor->options.field.lng)); \
    assert ((!btor->options.field.desc && !clone->options.field.desc)     \
            || (btor->options.field.desc                                  \
                && !strcmp (clone->options.field.desc,                    \
                            btor->options.field.desc)));                  \
    BTOR_CHKCLONE_STATE (options.field.val);                              \
    BTOR_CHKCLONE_STATE (options.field.dflt);                             \
    BTOR_CHKCLONE_STATE (options.field.min);                              \
    BTOR_CHKCLONE_STATE (options.field.max);                              \
  } while (0)

static void
btor_chkclone_opts (Btor *btor)
{
  assert (btor);

  Btor *clone;

  clone = btor->clone;
  assert (clone);

  BTOR_CHKCLONE_OPT (model_gen);
  BTOR_CHKCLONE_OPT (model_gen_all_reads);

  BTOR_CHKCLONE_OPT (incremental);
  BTOR_CHKCLONE_OPT (incremental_all);
  BTOR_CHKCLONE_OPT (incremental_in_depth);
  BTOR_CHKCLONE_OPT (incremental_look_ahead);
  BTOR_CHKCLONE_OPT (incremental_interval);

  BTOR_CHKCLONE_OPT (input_format);

  BTOR_CHKCLONE_OPT (output_number_format);
  BTOR_CHKCLONE_OPT (output_format);

  BTOR_CHKCLONE_OPT (rewrite_level);
  BTOR_CHKCLONE_OPT (rewrite_level_pbr);

  BTOR_CHKCLONE_OPT (beta_reduce_all);
#ifdef BTOR_ENABLE_BETA_REDUCTION_PROBING
  BTOR_CHKCLONE_OPT (probe_beta_reduce_all);
  BTOR_CHKCLONE_OPT (pbra_lod_limit);
  BTOR_CHKCLONE_OPT (pbra_sat_limit);
  BTOR_CHKCLONE_OPT (pbra_ops_factor);
#endif

#ifdef BTOR_ENABLE_DUAL_PROPAGATION
  BTOR_CHKCLONE_OPT (dual_prop);
#endif
  BTOR_CHKCLONE_OPT (just);
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  BTOR_CHKCLONE_OPT (ucopt);
#endif

  BTOR_CHKCLONE_OPT (force_cleanup);
  BTOR_CHKCLONE_OPT (pretty_print);
#ifndef NBTORLOG
  BTOR_CHKCLONE_OPT (loglevel);
#endif
  BTOR_CHKCLONE_OPT (verbosity);

  BTOR_CHKCLONE_OPT (simplify_constraints);
  BTOR_CHKCLONE_OPT (force_internal_cleanup);
#ifdef BTOR_CHECK_FAILED
  BTOR_CHKCLONE_OPT (chk_failed_assumptions);
#endif
}

#define BTOR_CHKCLONE_AIG(field)                   \
  do                                               \
  {                                                \
    assert (real_clone->field == real_aig->field); \
  } while (0)

#define BTOR_CHKCLONE_AIGPID(field)                        \
  do                                                       \
  {                                                        \
    if (!real_aig->field)                                  \
    {                                                      \
      assert (!real_clone->field);                         \
      break;                                               \
    }                                                      \
    assert (BTOR_IS_CONST_AIG (real_aig->field)            \
            || real_aig->field != real_clone->field);      \
    assert (real_aig->field->id == real_clone->field->id); \
  } while (0)

#define BTOR_CHKCLONE_AIGINV(field)                       \
  do                                                      \
  {                                                       \
    if (!real_aig->field)                                 \
    {                                                     \
      assert (!real_clone->field);                        \
      break;                                              \
    }                                                     \
    assert (BTOR_IS_INVERTED_AIG (real_aig->field)        \
            == BTOR_IS_INVERTED_AIG (real_clone->field)); \
    BTOR_CHKCLONE_AIGPID (field);                         \
  } while (0)

static void
btor_chkclone_aig (BtorAIG *aig, BtorAIG *clone)
{
  int i;
  BtorAIG *real_aig, *real_clone;

  real_aig   = BTOR_REAL_ADDR_AIG (aig);
  real_clone = BTOR_REAL_ADDR_AIG (clone);
  assert ((real_aig == BTOR_AIG_FALSE && real_clone == BTOR_AIG_FALSE)
          || real_aig != real_clone);

  if (real_aig != BTOR_AIG_FALSE)
  {
    BTOR_CHKCLONE_AIG (id);
    BTOR_CHKCLONE_AIG (refs);

    for (i = 0; i < 2; i++) BTOR_CHKCLONE_AIGINV (children[i]);

    BTOR_CHKCLONE_AIGPID (next);

    BTOR_CHKCLONE_AIG (cnf_id);
    BTOR_CHKCLONE_AIG (mark);
    BTOR_CHKCLONE_AIG (local);
  }
}

#define BTOR_CHKCLONE_AIG_UNIQUE_TABLE(table, clone)        \
  do                                                        \
  {                                                         \
    int i;                                                  \
    BtorAIG *next, *clone_next;                             \
    assert (table.size == clone.size);                      \
    assert (table.num_elements == clone.num_elements);      \
    for (i = 0; i < table.size; i++)                        \
    {                                                       \
      if (!table.chains[i])                                 \
      {                                                     \
        assert (!clone.chains[i]);                          \
        continue;                                           \
      }                                                     \
      btor_chkclone_aig (table.chains[i], clone.chains[i]); \
      next       = table.chains[i]->next;                   \
      clone_next = clone.chains[i]->next;                   \
      while (next)                                          \
      {                                                     \
        assert (clone_next);                                \
        btor_chkclone_aig (next, clone_next);               \
        next       = next->next;                            \
        clone_next = clone_next->next;                      \
      }                                                     \
      assert (!clone_next);                                 \
    }                                                       \
  } while (0)

#define BTOR_CHKCLONE_AIG_CNF_ID_TABLE(table, clone)               \
  do                                                               \
  {                                                                \
    int i;                                                         \
    assert (BTOR_COUNT_STACK (table) == 0);                        \
    assert (BTOR_COUNT_STACK (table) == BTOR_COUNT_STACK (clone)); \
    assert (BTOR_SIZE_STACK (table) == BTOR_SIZE_STACK (clone));   \
    for (i = 0; i < BTOR_SIZE_STACK (table); i++)                  \
    {                                                              \
      if (!table.start[i])                                         \
      {                                                            \
        assert (!clone.start[i]);                                  \
        continue;                                                  \
      }                                                            \
      assert (BTOR_IS_INVERTED_AIG (table.start[i])                \
              == BTOR_IS_INVERTED_AIG (clone.start[i]));           \
      assert (table.start[i] != clone.start[i]);                   \
      assert (table.start[i]->id == clone.start[i]->id);           \
    }                                                              \
  } while (0)

#define BTOR_CHKCLONE_EXP(field)                   \
  do                                               \
  {                                                \
    assert (real_exp->field == real_clone->field); \
  } while (0)

#define BTOR_CHKCLONE_EXPID(exp, clone)                                        \
  do                                                                           \
  {                                                                            \
    assert (BTOR_REAL_ADDR_NODE (exp)->id == BTOR_REAL_ADDR_NODE (clone)->id); \
  } while (0)

#define BTOR_CHKCLONE_EXPPID(field)                            \
  do                                                           \
  {                                                            \
    if (!real_exp->field)                                      \
    {                                                          \
      assert (!real_clone->field);                             \
      break;                                                   \
    }                                                          \
    assert (real_exp->field != real_clone->field);             \
    BTOR_CHKCLONE_EXPID (real_exp->field, real_clone->field);  \
    assert (BTOR_REAL_ADDR_NODE (real_exp->field)->btor->clone \
            == BTOR_REAL_ADDR_NODE (real_clone->field)->btor); \
  } while (0)

#define BTOR_CHKCLONE_EXPPINV(field)                       \
  do                                                       \
  {                                                        \
    BTOR_CHKCLONE_EXPPID (field);                          \
    assert (BTOR_IS_INVERTED_NODE (real_exp->field)        \
            == BTOR_IS_INVERTED_NODE (real_clone->field)); \
  } while (0)

#define BTOR_CHKCLONE_EXPPTAG(field)                   \
  do                                                   \
  {                                                    \
    BTOR_CHKCLONE_EXPPID (field);                      \
    assert (BTOR_GET_TAG_NODE (real_exp->field)        \
            == BTOR_GET_TAG_NODE (real_clone->field)); \
  } while (0)

/* Note: no hash table to be cloned uses data->asInt (check data->asPtr only) */
#define BTOR_CHKCLONE_NODE_PTR_HASH_TABLE(table, clone)                  \
  do                                                                     \
  {                                                                      \
    BtorPtrHashBucket *bb, *cbb;                                         \
    if (!(table))                                                        \
    {                                                                    \
      assert (!(clone));                                                 \
      break;                                                             \
    }                                                                    \
    assert ((table)->size == (clone)->size);                             \
    assert ((table)->count == (clone)->count);                           \
    assert ((table)->hash == (clone)->hash);                             \
    assert ((table)->cmp == (clone)->cmp);                               \
    for (bb = (table)->first, cbb = (clone)->first; bb;                  \
         bb = bb->next, cbb = cbb->next)                                 \
    {                                                                    \
      assert (cbb);                                                      \
      BTOR_CHKCLONE_EXPID ((BtorNode *) bb->key, (BtorNode *) cbb->key); \
      assert (!bb->next || cbb->next);                                   \
    }                                                                    \
  } while (0)

void
btor_chkclone_exp (BtorNode *exp, BtorNode *clone)
{
  assert (exp);
  assert (clone);
  assert (exp != clone);
  assert ((!BTOR_IS_INVERTED_NODE (exp) && !BTOR_IS_INVERTED_NODE (clone))
          || (BTOR_IS_INVERTED_NODE (exp) && BTOR_IS_INVERTED_NODE (clone)));

  int i, len;
  BtorNode *real_exp, *real_clone, *e, *ce;
  BtorHashTableIterator it, cit;

  real_exp   = BTOR_REAL_ADDR_NODE (exp);
  real_clone = BTOR_REAL_ADDR_NODE (clone);
  assert (real_exp != real_clone);
  assert (real_exp->id == real_clone->id);
  assert (real_exp->btor->clone == real_clone->btor);

  BTOR_CHKCLONE_EXP (kind);
  BTOR_CHKCLONE_EXP (mark);
  BTOR_CHKCLONE_EXP (aux_mark);
  BTOR_CHKCLONE_EXP (fun_mark);
  BTOR_CHKCLONE_EXP (beta_mark);
  BTOR_CHKCLONE_EXP (eval_mark);
  BTOR_CHKCLONE_EXP (synth_mark);
  BTOR_CHKCLONE_EXP (reachable);
  BTOR_CHKCLONE_EXP (tseitin);
  BTOR_CHKCLONE_EXP (lazy_tseitin);
  BTOR_CHKCLONE_EXP (vread);
  BTOR_CHKCLONE_EXP (vread_index);
  BTOR_CHKCLONE_EXP (constraint);
  BTOR_CHKCLONE_EXP (erased);
  BTOR_CHKCLONE_EXP (disconnected);
  BTOR_CHKCLONE_EXP (unique);
  BTOR_CHKCLONE_EXP (bytes);
  BTOR_CHKCLONE_EXP (parameterized);
  BTOR_CHKCLONE_EXP (lambda_below);
  BTOR_CHKCLONE_EXP (merge);
  BTOR_CHKCLONE_EXP (is_write);
  BTOR_CHKCLONE_EXP (is_read);

  if (real_exp->bits)
  {
    len = strlen (real_exp->bits);
    assert ((size_t) len == strlen (real_clone->bits));
    for (i = 0; i < len; i++) assert (real_exp->bits[i] == real_clone->bits[i]);
  }
  else
  {
    assert ((real_exp->av && real_clone->av)
            || (!real_exp->av && !real_clone->av));
  }

  BTOR_CHKCLONE_EXP (id);
  BTOR_CHKCLONE_EXP (len);
  BTOR_CHKCLONE_EXP (refs);
  BTOR_CHKCLONE_EXP (ext_refs);
  BTOR_CHKCLONE_EXP (parents);
  BTOR_CHKCLONE_EXP (arity);

  if (!BTOR_IS_FUN_NODE (real_exp))
  {
    if (real_exp->av)
    {
      assert (real_exp->av->len == real_clone->av->len);
      for (i = 0; i < real_exp->len; i++)
        btor_chkclone_aig (real_exp->av->aigs[i], real_clone->av->aigs[i]);
    }
    else
      assert (real_exp->av == real_clone->av);
  }
  else if (real_exp->rho)
    BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (real_exp->rho, real_clone->rho);

  BTOR_CHKCLONE_EXPPID (next);
  /* Note: parent node used during BFS only, pointer is not reset after bfs,
   *	   hence not cloned, do not check */
  BTOR_CHKCLONE_EXPPINV (simplified);
  assert (real_exp->btor->clone == real_clone->btor);
  BTOR_CHKCLONE_EXPPTAG (first_parent);
  BTOR_CHKCLONE_EXPPTAG (last_parent);

  if (BTOR_IS_PROXY_NODE (real_exp)) return;

  if (!BTOR_IS_BV_CONST_NODE (real_exp))
  {
    assert (!real_clone->symbol
            || !strcmp (real_exp->symbol, real_clone->symbol));

    if (!BTOR_IS_BV_VAR_NODE (real_exp) && !BTOR_IS_UF_NODE (real_exp)
        && !BTOR_IS_PARAM_NODE (real_exp))
    {
      if (real_exp->arity)
      {
        for (i = 0; i < real_exp->arity; i++) BTOR_CHKCLONE_EXPPINV (e[i]);
      }
      else
      {
        BTOR_CHKCLONE_EXP (upper);
        if (!BTOR_IS_ARRAY_EQ_NODE (real_exp))
          BTOR_CHKCLONE_EXP (lower);
        else
        {
          assert (real_exp->vreads->exp1->id == real_clone->vreads->exp1->id);
          assert (real_exp->vreads->exp2->id == real_clone->vreads->exp2->id);
        }
      }
    }

    for (i = 0; i < real_exp->arity; i++)
    {
      BTOR_CHKCLONE_EXPPTAG (prev_parent[i]);
      BTOR_CHKCLONE_EXPPTAG (next_parent[i]);
    }
  }

#if 0
  if (BTOR_IS_FUN_NODE (real_exp))
    {
      BTOR_CHKCLONE_EXP (index_len);
      BTOR_CHKCLONE_EXPPTAG (first_aeq_acond_parent);
      BTOR_CHKCLONE_EXPPTAG (last_aeq_acond_parent);

      if (!BTOR_IS_ARRAY_VAR_NODE (real_exp))
	{
	  for (i = 0; i < real_exp->arity; i++)
	    {
	      BTOR_CHKCLONE_EXPPTAG (prev_aeq_acond_parent[i]);
	      BTOR_CHKCLONE_EXPPTAG (next_aeq_acond_parent[i]);
	    }
	}
    }
#endif

  if (BTOR_IS_PARAM_NODE (real_exp))
  {
    if (((BtorParamNode *) real_exp)->lambda_exp)
    {
      assert (((BtorParamNode *) real_exp)->lambda_exp
              != ((BtorParamNode *) real_clone)->lambda_exp);
      BTOR_CHKCLONE_EXPID (((BtorParamNode *) real_exp)->lambda_exp,
                           ((BtorParamNode *) real_clone)->lambda_exp);
    }
    else
      assert (!((BtorParamNode *) real_clone)->lambda_exp);

    if (((BtorParamNode *) real_exp)->assigned_exp)
    {
      assert (((BtorParamNode *) real_exp)->assigned_exp
              != ((BtorParamNode *) real_clone)->assigned_exp);
      BTOR_CHKCLONE_EXPID (((BtorParamNode *) real_exp)->assigned_exp,
                           ((BtorParamNode *) real_clone)->assigned_exp);
    }
    else
      assert (!((BtorParamNode *) real_clone)->assigned_exp);
  }

  if (BTOR_IS_ARGS_NODE (real_exp))
    assert (((BtorArgsNode *) real_exp)->num_args
            == ((BtorArgsNode *) real_clone)->num_args);

  if (BTOR_IS_LAMBDA_NODE (real_exp))
  {
    if (((BtorLambdaNode *) real_exp)->synth_apps)
    {
      init_node_hash_table_iterator (&it,
                                     ((BtorLambdaNode *) real_exp)->synth_apps);
      init_node_hash_table_iterator (
          &cit, ((BtorLambdaNode *) real_clone)->synth_apps);
      while (has_next_node_hash_table_iterator (&it))
      {
        assert (has_next_node_hash_table_iterator (&cit));
        e  = next_node_hash_table_iterator (&it);
        ce = next_node_hash_table_iterator (&cit);
        if (e)
        {
          assert (ce);
          assert (e != ce);
          BTOR_CHKCLONE_EXPID (e, ce);
        }
        else
          assert (!ce);
      }
      assert (!has_next_hash_table_iterator (&cit));
    }

    if (((BtorLambdaNode *) real_exp)->head)
    {
      assert (((BtorLambdaNode *) real_exp)->head
              != ((BtorLambdaNode *) real_clone)->head);
      BTOR_CHKCLONE_EXPID (((BtorLambdaNode *) real_exp)->head,
                           ((BtorLambdaNode *) real_clone)->head);
    }
    else
      assert (!((BtorLambdaNode *) real_clone)->head);

    if (((BtorLambdaNode *) real_exp)->body)
    {
      assert (((BtorLambdaNode *) real_exp)->body
              != ((BtorLambdaNode *) real_clone)->body);
      BTOR_CHKCLONE_EXPID (((BtorLambdaNode *) real_exp)->body,
                           ((BtorLambdaNode *) real_clone)->body);
    }
    else
      assert (!((BtorLambdaNode *) real_clone)->body);
  }
}

#define BTOR_CHKCLONE_NODE_PTR_STACK(stack, clone)                 \
  do                                                               \
  {                                                                \
    int i;                                                         \
    assert (BTOR_COUNT_STACK (stack) == BTOR_COUNT_STACK (clone)); \
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++)                 \
    {                                                              \
      if (!BTOR_PEEK_STACK (stack, i))                             \
      {                                                            \
        assert (!BTOR_PEEK_STACK (clone, i));                      \
        continue;                                                  \
      }                                                            \
      BTOR_CHKCLONE_EXPID (BTOR_PEEK_STACK (stack, i),             \
                           BTOR_PEEK_STACK (clone, i));            \
    }                                                              \
  } while (0)

#define BTOR_CHKCLONE_NODE_ID_TABLE(stack, clone)                  \
  do                                                               \
  {                                                                \
    int i;                                                         \
    assert (BTOR_COUNT_STACK (stack) == BTOR_COUNT_STACK (clone)); \
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++)                 \
    {                                                              \
      if (!BTOR_PEEK_STACK (stack, i))                             \
      {                                                            \
        assert (!BTOR_PEEK_STACK (clone, i));                      \
        continue;                                                  \
      }                                                            \
      btor_chkclone_exp (BTOR_PEEK_STACK (stack, i),               \
                         BTOR_PEEK_STACK (clone, i));              \
    }                                                              \
  } while (0)

/* Note: no need to check next pointers here as we catch all of them when
 *	 traversing through nodes id table. */
#define BTOR_CHKCLONE_NODE_UNIQUE_TABLE(table, clone)         \
  do                                                          \
  {                                                           \
    int i;                                                    \
    assert (table.size == clone.size);                        \
    assert (table.num_elements == clone.num_elements);        \
    for (i = 0; i < table.size; i++)                          \
    {                                                         \
      if (!table.chains[i])                                   \
      {                                                       \
        assert (!clone.chains[i]);                            \
        continue;                                             \
      }                                                       \
      BTOR_CHKCLONE_EXPID (table.chains[i], clone.chains[i]); \
    }                                                         \
  } while (0)

static void
btor_chkclone_assignment_lists (Btor *btor)
{
  BtorBVAssignment *bvass, *cbvass;
  BtorArrayAssignment *arrass, *carrass;
  char **ind, **val, **cind, **cval;
  int i;

  assert (btor->bv_assignments->count == btor->clone->bv_assignments->count);
  for (bvass = btor->bv_assignments->first,
      cbvass = btor->clone->bv_assignments->first;
       bvass;
       bvass = bvass->next, cbvass = cbvass->next)
  {
    assert (cbvass);
    assert (!strcmp (btor_get_bv_assignment_str (bvass),
                     btor_get_bv_assignment_str (cbvass)));
  }

  assert (btor->array_assignments->count
          == btor->clone->array_assignments->count);
  for (arrass = btor->array_assignments->first,
      carrass = btor->clone->array_assignments->first;
       arrass;
       arrass = arrass->next, carrass = carrass->next)
  {
    assert (carrass);
    assert (arrass->size == carrass->size);
    btor_get_array_assignment_indices_values (arrass, &ind, &val, arrass->size);
    btor_get_array_assignment_indices_values (
        carrass, &cind, &cval, carrass->size);
    for (i = 0; i < arrass->size; i++)
    {
      assert (!strcmp (ind[i], cind[i]));
      assert (!strcmp (val[i], cval[i]));
    }
  }
}

static void
btor_chkclone_tables (Btor *btor)
{
  BtorHashTableIterator it, cit, nit, cnit;

  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->bv_vars, btor->clone->bv_vars);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->lambdas, btor->clone->lambdas);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->substitutions,
                                     btor->clone->substitutions);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->lod_cache, btor->clone->lod_cache);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->varsubst_constraints,
                                     btor->clone->varsubst_constraints);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->embedded_constraints,
                                     btor->clone->embedded_constraints);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->unsynthesized_constraints,
                                     btor->clone->unsynthesized_constraints);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->synthesized_constraints,
                                     btor->clone->synthesized_constraints);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->assumptions,
                                     btor->clone->assumptions);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->var_rhs, btor->clone->var_rhs);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->array_rhs, btor->clone->array_rhs);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->cache, btor->clone->cache);

  if (btor->parameterized)
  {
    assert (btor->clone->parameterized);
    assert (btor->parameterized->size == btor->clone->parameterized->size);
    assert (btor->parameterized->count == btor->clone->parameterized->count);
    assert (btor->parameterized->hash == btor->clone->parameterized->hash);
    assert (btor->parameterized->cmp == btor->clone->parameterized->cmp);
    assert (!btor->parameterized->first || btor->clone->parameterized->first);
    init_node_hash_table_iterator (&it, btor->parameterized);
    init_node_hash_table_iterator (&cit, btor->clone->parameterized);
    while (has_next_node_hash_table_iterator (&it))
    {
      assert (has_next_node_hash_table_iterator (&cit));
      BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (
          (BtorPtrHashTable *) it.bucket->data.asPtr,
          (BtorPtrHashTable *) cit.bucket->data.asPtr);
      BTOR_CHKCLONE_EXPID (next_node_hash_table_iterator (&it),
                           next_node_hash_table_iterator (&cit));
    }
    assert (!has_next_hash_table_iterator (&cit));
  }
  else
    assert (!btor->clone->parameterized);

  if (btor->bv_model)
  {
    assert (btor->clone->bv_model);
    assert (btor->bv_model->size == btor->clone->bv_model->size);
    assert (btor->bv_model->count == btor->clone->bv_model->count);
    assert (btor->bv_model->hash == btor->clone->bv_model->hash);
    assert (btor->bv_model->cmp == btor->clone->bv_model->cmp);
    init_node_hash_table_iterator (&it, btor->bv_model);
    init_node_hash_table_iterator (&cit, btor->clone->bv_model);
    while (has_next_node_hash_table_iterator (&it))
    {
      assert (has_next_node_hash_table_iterator (&cit));
      BTOR_CHKCLONE_EXPID ((BtorNode *) it.cur, (BtorNode *) cit.cur);
      assert (it.bucket->data.asPtr);
      assert (cit.bucket->data.asPtr);
      assert (!btor_compare_bv ((BitVector *) it.bucket->data.asPtr,
                                (BitVector *) cit.bucket->data.asPtr));
      (void) next_node_hash_table_iterator (&it);
      (void) next_node_hash_table_iterator (&cit);
    }
    assert (!has_next_node_hash_table_iterator (&cit));
  }
  else
    assert (!btor->clone->bv_model);

  if (btor->fun_model)
  {
    assert (btor->clone->fun_model);
    assert (btor->fun_model->size == btor->clone->fun_model->size);
    assert (btor->fun_model->count == btor->clone->fun_model->count);
    assert (btor->fun_model->hash == btor->clone->fun_model->hash);
    assert (btor->fun_model->cmp == btor->clone->fun_model->cmp);
    init_node_hash_table_iterator (&it, btor->fun_model);
    init_node_hash_table_iterator (&cit, btor->clone->fun_model);
    while (has_next_node_hash_table_iterator (&it))
    {
      assert (has_next_node_hash_table_iterator (&cit));
      assert (it.bucket->data.asPtr);
      assert (cit.bucket->data.asPtr);
      init_hash_table_iterator (&nit,
                                (BtorPtrHashTable *) it.bucket->data.asPtr);
      init_hash_table_iterator (&cnit,
                                (BtorPtrHashTable *) cit.bucket->data.asPtr);
      while (has_next_hash_table_iterator (&nit))
      {
        assert (has_next_hash_table_iterator (&cnit));
        assert (!btor_compare_bv ((BitVector *) nit.bucket->data.asPtr,
                                  (BitVector *) cnit.bucket->data.asPtr));
        assert (!btor_compare_bv_tuple ((BitVectorTuple *) nit.cur,
                                        (BitVectorTuple *) cnit.cur));
        (void) next_hash_table_iterator (&nit);
        (void) next_hash_table_iterator (&cnit);
      }
      assert (!has_next_hash_table_iterator (&cnit));
      BTOR_CHKCLONE_EXPID (next_node_hash_table_iterator (&it),
                           next_node_hash_table_iterator (&cit));
    }
    assert (!has_next_hash_table_iterator (&cit));
  }
  else
    assert (!btor->clone->fun_model);
}

void
btor_chkclone_opt (const BtorOpt *opt, const BtorOpt *clone)
{
  assert (opt->internal == clone->internal);
  assert (!strcmp (opt->shrt, clone->shrt));
  assert (!strcmp (opt->lng, clone->lng));
  assert (!strcmp (opt->desc, clone->desc));
  assert (opt->val == clone->val);
  assert (opt->dflt == clone->dflt);
  assert (opt->min == clone->min);
  assert (opt->max == clone->max);
}

void
btor_chkclone_sort (const BtorSort *sort, const BtorSort *clone)
{
  int i;
  assert (sort->id == clone->id);
  assert (sort->kind == clone->kind);
  assert (sort->refs == clone->refs);
  assert (sort->ext_refs == clone->ext_refs);
  assert (sort->parents == clone->parents);

  switch (sort->kind)
  {
    case BTOR_BITVEC_SORT:
      assert (sort->bitvec.len == clone->bitvec.len);
      break;

    case BTOR_ARRAY_SORT:
      assert (sort->array.index->id == clone->array.index->id);
      assert (sort->array.element->id == clone->array.element->id);
      break;

    case BTOR_FUN_SORT:
      assert (sort->fun.arity == clone->fun.arity);
      assert (sort->fun.domain->id == clone->fun.domain->id);
      assert (sort->fun.codomain->id == clone->fun.codomain->id);
      break;

    case BTOR_TUPLE_SORT:
      assert (sort->tuple.num_elements == clone->tuple.num_elements);
      for (i = 0; i < sort->tuple.num_elements; i++)
        assert (sort->tuple.elements[i]->id == clone->tuple.elements[i]->id);
      break;

    case BTOR_LST_SORT:
      assert (sort->lst.head->id == clone->lst.head->id);
      assert (sort->lst.tail->id == clone->lst.tail->id);
      break;

    default: break;
  }
}

void
btor_chkclone (Btor *btor)
{
  if (!btor->clone) return;

  btor_chkclone_mem (btor);
  btor_chkclone_state (btor);
  btor_chkclone_stats (btor);
  btor_chkclone_opts (btor);
  btor_chkclone_assignment_lists (btor);
  BTOR_CHKCLONE_AIG_UNIQUE_TABLE (
      btor_get_aig_mgr_aigvec_mgr (btor->avmgr)->table,
      btor_get_aig_mgr_aigvec_mgr (btor->clone->avmgr)->table);
  BTOR_CHKCLONE_AIG_CNF_ID_TABLE (
      btor_get_aig_mgr_aigvec_mgr (btor->avmgr)->id2aig,
      btor_get_aig_mgr_aigvec_mgr (btor->clone->avmgr)->id2aig);
  BTOR_CHKCLONE_NODE_ID_TABLE (btor->nodes_id_table,
                               btor->clone->nodes_id_table);
  BTOR_CHKCLONE_NODE_UNIQUE_TABLE (btor->nodes_unique_table,
                                   btor->clone->nodes_unique_table);
  BTOR_CHKCLONE_NODE_PTR_STACK (btor->functions_with_model,
                                btor->clone->functions_with_model);
  btor_chkclone_tables (btor);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
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
#include "btoropt.h"
#include "btorslv.h"
#include "utils/btoriter.h"

static void
btor_chkclone_mem (Btor *btor)
{
  assert (btor);
  assert (btor->clone);
  assert (btor->mm);
  assert (btor->clone->mm);
  assert (
      btor->mm->allocated
          - (btor->msg->prefix
                 ? (strlen (btor->msg->prefix) + 1) * sizeof (char)
                 : 0)
      == btor->clone->mm->allocated
             - (btor->clone->msg->prefix
                    ? (strlen (btor->clone->msg->prefix) + 1) * sizeof (char)
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

  BTOR_CHKCLONE_STATE (rec_rw_calls);
  BTOR_CHKCLONE_STATE (valid_assignments);
  BTOR_CHKCLONE_STATE (vis_idx);
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
  BTOR_CHKCLONE_STATS (var_substitutions);
  BTOR_CHKCLONE_STATS (uf_substitutions);
  BTOR_CHKCLONE_STATS (ec_substitutions);
  BTOR_CHKCLONE_STATS (linear_equations);
  BTOR_CHKCLONE_STATS (gaussian_eliminations);
  BTOR_CHKCLONE_STATS (eliminated_slices);
  BTOR_CHKCLONE_STATS (skeleton_constraints);
  BTOR_CHKCLONE_STATS (adds_normalized);
  BTOR_CHKCLONE_STATS (ands_normalized);
  BTOR_CHKCLONE_STATS (muls_normalized);
  BTOR_CHKCLONE_STATS (apply_props_construct);
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  BTOR_CHKCLONE_STATS (bv_uc_props);
  BTOR_CHKCLONE_STATS (fun_uc_props);
#endif
  BTOR_CHKCLONE_STATS (lambdas_merged);

  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, varsubst);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, embedded);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, unsynthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, synthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, varsubst);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, embedded);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, unsynthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, synthesized);

  BTOR_CHKCLONE_STATS (expressions);
  BTOR_CHKCLONE_STATS (node_bytes_alloc);
  BTOR_CHKCLONE_STATS (beta_reduce_calls);
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

  BTOR_CHKCLONE_OPT (dual_prop);
  BTOR_CHKCLONE_OPT (just);
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  BTOR_CHKCLONE_OPT (ucopt);
#endif

  /* Note: auto_cleanup.val = 1 in clone! */
  BTOR_CHKCLONE_STATE (options.auto_cleanup.internal);
  assert (
      (!btor->options.auto_cleanup.shrt && !clone->options.auto_cleanup.shrt)
      || (btor->options.auto_cleanup.shrt
          && !strcmp (clone->options.auto_cleanup.shrt,
                      btor->options.auto_cleanup.shrt)));
  assert (!strcmp (clone->options.auto_cleanup.lng,
                   btor->options.auto_cleanup.lng));
  assert (
      (!btor->options.auto_cleanup.desc && !clone->options.auto_cleanup.desc)
      || (btor->options.auto_cleanup.desc
          && !strcmp (clone->options.auto_cleanup.desc,
                      btor->options.auto_cleanup.desc)));
  BTOR_CHKCLONE_STATE (options.auto_cleanup.dflt);
  BTOR_CHKCLONE_STATE (options.auto_cleanup.min);
  BTOR_CHKCLONE_STATE (options.auto_cleanup.max);

  BTOR_CHKCLONE_OPT (pretty_print);
#ifndef NBTORLOG
  BTOR_CHKCLONE_OPT (loglevel);
#endif
  BTOR_CHKCLONE_OPT (verbosity);

  BTOR_CHKCLONE_OPT (simplify_constraints);
  BTOR_CHKCLONE_OPT (auto_cleanup_internal);
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
    BTOR_CHKCLONE_AIG (next);
    BTOR_CHKCLONE_AIG (cnf_id);
    BTOR_CHKCLONE_AIG (mark);
    BTOR_CHKCLONE_AIG (is_var);
    BTOR_CHKCLONE_AIG (local);
    if (!real_aig->is_var)
      for (i = 0; i < 2; i++) BTOR_CHKCLONE_AIG (children[i]);
  }
}

#define BTOR_CHKCLONE_AIG_UNIQUE_TABLE(table, clone)   \
  do                                                   \
  {                                                    \
    int i;                                             \
    assert (table.size == clone.size);                 \
    assert (table.num_elements == clone.num_elements); \
    for (i = 0; i < table.size; i++)                   \
      assert (table.chains[i] == clone.chains[i]);     \
  } while (0)

#define BTOR_CHKCLONE_AIG_ID_TABLE(table, clone)                   \
  do                                                               \
  {                                                                \
    int i;                                                         \
    assert (BTOR_COUNT_STACK (table) == BTOR_COUNT_STACK (clone)); \
    assert (BTOR_SIZE_STACK (table) == BTOR_SIZE_STACK (clone));   \
    for (i = 0; i < BTOR_COUNT_STACK (table); i++)                 \
      btor_chkclone_aig (table.start[i], clone.start[i]);          \
  } while (0)

#define BTOR_CHKCLONE_AIG_CNF_ID_TABLE(table, clone)               \
  do                                                               \
  {                                                                \
    int i;                                                         \
    assert (BTOR_COUNT_STACK (table) == 0);                        \
    assert (BTOR_COUNT_STACK (table) == BTOR_COUNT_STACK (clone)); \
    assert (BTOR_SIZE_STACK (table) == BTOR_SIZE_STACK (clone));   \
    for (i = 0; i < BTOR_SIZE_STACK (table); i++)                  \
      assert (table.start[i] == clone.start[i]);                   \
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

#define BTOR_CHKCLONE_NODE_PTR_HASH_TABLE(table, clone)                  \
  do                                                                     \
  {                                                                      \
    BtorHashTableIterator iter, citer;                                   \
    if (!(table))                                                        \
    {                                                                    \
      assert (!(clone));                                                 \
      break;                                                             \
    }                                                                    \
    assert ((table)->size == (clone)->size);                             \
    assert ((table)->count == (clone)->count);                           \
    assert ((table)->hash == (clone)->hash);                             \
    assert ((table)->cmp == (clone)->cmp);                               \
    btor_init_node_hash_table_iterator (&iter, (table));                 \
    btor_init_node_hash_table_iterator (&citer, (clone));                \
    while (btor_has_next_node_hash_table_iterator (&iter))               \
    {                                                                    \
      assert (btor_has_next_node_hash_table_iterator (&citer));          \
      BTOR_CHKCLONE_EXPID (btor_next_node_hash_table_iterator (&iter),   \
                           btor_next_node_hash_table_iterator (&citer)); \
    }                                                                    \
    assert (!btor_has_next_node_hash_table_iterator (&citer));           \
  } while (0)

void
btor_chkclone_exp (BtorNode *exp, BtorNode *clone)
{
  assert (exp);
  assert (clone);
  assert (exp != clone);
  assert ((!BTOR_IS_INVERTED_NODE (exp) && !BTOR_IS_INVERTED_NODE (clone))
          || (BTOR_IS_INVERTED_NODE (exp) && BTOR_IS_INVERTED_NODE (clone)));

  unsigned i;
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
  BTOR_CHKCLONE_EXP (beta_mark);
  BTOR_CHKCLONE_EXP (eval_mark);
  BTOR_CHKCLONE_EXP (reachable);
  BTOR_CHKCLONE_EXP (constraint);
  BTOR_CHKCLONE_EXP (erased);
  BTOR_CHKCLONE_EXP (disconnected);
  BTOR_CHKCLONE_EXP (unique);
  BTOR_CHKCLONE_EXP (bytes);
  BTOR_CHKCLONE_EXP (parameterized);
  BTOR_CHKCLONE_EXP (lambda_below);

  if (BTOR_IS_BV_CONST_NODE (real_exp))
  {
    assert (btor_const_get_bits (real_exp)->width
            == btor_const_get_bits (real_clone)->width);
    assert (btor_compare_bv (btor_const_get_bits (real_exp),
                             btor_const_get_bits (real_clone))
            == 0);
    if (btor_const_get_invbits (real_exp))
    {
      assert (btor_const_get_invbits (real_exp)->width
              == btor_const_get_invbits (real_clone)->width);
      assert (btor_compare_bv (btor_const_get_invbits (real_exp),
                               btor_const_get_invbits (real_clone))
              == 0);
    }
  }
  else
  {
    assert ((real_exp->av && real_clone->av)
            || (!real_exp->av && !real_clone->av));
  }

  BTOR_CHKCLONE_EXP (id);
  BTOR_CHKCLONE_EXP (refs);
  BTOR_CHKCLONE_EXP (ext_refs);
  BTOR_CHKCLONE_EXP (parents);
  BTOR_CHKCLONE_EXP (arity);

  if (!BTOR_IS_FUN_NODE (real_exp))
  {
    if (real_exp->av)
    {
      assert (real_exp->av->len == real_clone->av->len);
      for (i = 0; i < real_exp->av->len; i++)
        btor_chkclone_aig (real_exp->av->aigs[i], real_clone->av->aigs[i]);
    }
    else
      assert (real_exp->av == real_clone->av);
  }
  else if (real_exp->rho)
    BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (real_exp->rho, real_clone->rho);

  BTOR_CHKCLONE_EXPPID (next);
  BTOR_CHKCLONE_EXPPINV (simplified);
  assert (real_exp->btor->clone == real_clone->btor);
  BTOR_CHKCLONE_EXPPTAG (first_parent);
  BTOR_CHKCLONE_EXPPTAG (last_parent);

  if (BTOR_IS_PROXY_NODE (real_exp)) return;

  if (!BTOR_IS_BV_CONST_NODE (real_exp))
  {
    if (!BTOR_IS_BV_VAR_NODE (real_exp) && !BTOR_IS_UF_NODE (real_exp)
        && !BTOR_IS_PARAM_NODE (real_exp))
    {
      if (real_exp->arity)
      {
        for (i = 0; i < real_exp->arity; i++) BTOR_CHKCLONE_EXPPINV (e[i]);
      }
    }

    if (BTOR_IS_SLICE_NODE (real_exp))
    {
      assert (btor_slice_get_upper (real_exp)
              == btor_slice_get_upper (real_clone));
      assert (btor_slice_get_lower (real_exp)
              == btor_slice_get_lower (real_clone));
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

  if (BTOR_IS_LAMBDA_NODE (real_exp))
  {
    if (btor_lambda_get_static_rho (real_exp))
    {
      btor_init_node_hash_table_iterator (
          &it, btor_lambda_get_static_rho (real_exp));
      btor_init_node_hash_table_iterator (
          &cit, btor_lambda_get_static_rho (real_clone));
      while (btor_has_next_node_hash_table_iterator (&it))
      {
        assert (btor_has_next_node_hash_table_iterator (&cit));
        e  = btor_next_node_hash_table_iterator (&it);
        ce = btor_next_node_hash_table_iterator (&cit);
        if (e)
        {
          assert (ce);
          assert (e != ce);
          BTOR_CHKCLONE_EXPID (e, ce);
        }
        else
          assert (!ce);
      }
      assert (!btor_has_next_hash_table_iterator (&cit));
    }

#if 0
      if (((BtorLambdaNode *) real_exp)->head)
	{
	  assert (((BtorLambdaNode *) real_exp)->head
		  != ((BtorLambdaNode *) real_clone)->head);
	  BTOR_CHKCLONE_EXPID (((BtorLambdaNode *) real_exp)->head,
			    ((BtorLambdaNode *) real_clone)->head);
	}
      else
	assert (!((BtorLambdaNode *) real_clone)->head);
#endif

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
  char *sym, *csym;

  if (btor->symbols)
  {
    assert (btor->clone->symbols);
    assert (btor->symbols->size == btor->clone->symbols->size);
    assert (btor->symbols->count == btor->clone->symbols->count);
    assert (btor->symbols->hash == btor->clone->symbols->hash);
    assert (btor->symbols->cmp == btor->clone->symbols->cmp);
    assert (!btor->symbols->first || btor->clone->symbols->first);
    btor_init_hash_table_iterator (&it, btor->symbols);
    btor_init_hash_table_iterator (&cit, btor->clone->symbols);
    while (btor_has_next_hash_table_iterator (&it))
    {
      assert (btor_has_next_hash_table_iterator (&cit));
      assert (!strcmp ((char *) btor_next_hash_table_iterator (&it),
                       (char *) btor_next_hash_table_iterator (&cit)));
    }
    assert (!btor_has_next_hash_table_iterator (&cit));
  }
  else
    assert (!btor->clone->symbols);

  if (btor->node2symbol)
  {
    assert (btor->clone->node2symbol);
    assert (btor->node2symbol->size == btor->clone->node2symbol->size);
    assert (btor->node2symbol->count == btor->clone->node2symbol->count);
    assert (btor->node2symbol->hash == btor->clone->node2symbol->hash);
    assert (btor->node2symbol->cmp == btor->clone->node2symbol->cmp);
    assert (!btor->node2symbol->first || btor->clone->node2symbol->first);
    btor_init_node_hash_table_iterator (&it, btor->node2symbol);
    btor_init_node_hash_table_iterator (&cit, btor->clone->node2symbol);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      assert (btor_has_next_node_hash_table_iterator (&cit));
      sym  = it.bucket->data.asStr;
      csym = cit.bucket->data.asStr;
      assert (sym != csym);
      assert (!strcmp (sym, csym));
      assert (btor_find_in_ptr_hash_table (btor->symbols, sym));
      assert (btor_find_in_ptr_hash_table (btor->clone->symbols, sym));
      BTOR_CHKCLONE_EXPID (btor_next_node_hash_table_iterator (&it),
                           btor_next_node_hash_table_iterator (&cit));
    }
    assert (!btor_has_next_node_hash_table_iterator (&cit));
  }
  else
    assert (!btor->clone->node2symbol);

  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->bv_vars, btor->clone->bv_vars);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->lambdas, btor->clone->lambdas);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->feqs, btor->clone->feqs);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->substitutions,
                                     btor->clone->substitutions);
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
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->fun_rhs, btor->clone->fun_rhs);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->cache, btor->clone->cache);

  if (btor->parameterized)
  {
    assert (btor->clone->parameterized);
    assert (btor->parameterized->size == btor->clone->parameterized->size);
    assert (btor->parameterized->count == btor->clone->parameterized->count);
    assert (btor->parameterized->hash == btor->clone->parameterized->hash);
    assert (btor->parameterized->cmp == btor->clone->parameterized->cmp);
    assert (!btor->parameterized->first || btor->clone->parameterized->first);
    btor_init_node_hash_table_iterator (&it, btor->parameterized);
    btor_init_node_hash_table_iterator (&cit, btor->clone->parameterized);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      assert (btor_has_next_node_hash_table_iterator (&cit));
      BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (
          (BtorPtrHashTable *) it.bucket->data.asPtr,
          (BtorPtrHashTable *) cit.bucket->data.asPtr);
      BTOR_CHKCLONE_EXPID (btor_next_node_hash_table_iterator (&it),
                           btor_next_node_hash_table_iterator (&cit));
    }
    assert (!btor_has_next_node_hash_table_iterator (&cit));
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
    btor_init_node_hash_table_iterator (&it, btor->bv_model);
    btor_init_node_hash_table_iterator (&cit, btor->clone->bv_model);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      assert (btor_has_next_node_hash_table_iterator (&cit));
      BTOR_CHKCLONE_EXPID ((BtorNode *) it.cur, (BtorNode *) cit.cur);
      assert (it.bucket->data.asPtr);
      assert (cit.bucket->data.asPtr);
      assert (!btor_compare_bv ((BtorBitVector *) it.bucket->data.asPtr,
                                (BtorBitVector *) cit.bucket->data.asPtr));
      (void) btor_next_node_hash_table_iterator (&it);
      (void) btor_next_node_hash_table_iterator (&cit);
    }
    assert (!btor_has_next_node_hash_table_iterator (&cit));
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
    btor_init_node_hash_table_iterator (&it, btor->fun_model);
    btor_init_node_hash_table_iterator (&cit, btor->clone->fun_model);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      assert (btor_has_next_node_hash_table_iterator (&cit));
      assert (it.bucket->data.asPtr);
      assert (cit.bucket->data.asPtr);
      btor_init_hash_table_iterator (
          &nit, (BtorPtrHashTable *) it.bucket->data.asPtr);
      btor_init_hash_table_iterator (
          &cnit, (BtorPtrHashTable *) cit.bucket->data.asPtr);
      while (btor_has_next_hash_table_iterator (&nit))
      {
        assert (btor_has_next_hash_table_iterator (&cnit));
        assert (!btor_compare_bv ((BtorBitVector *) nit.bucket->data.asPtr,
                                  (BtorBitVector *) cnit.bucket->data.asPtr));
        assert (!btor_compare_bv_tuple ((BtorBitVectorTuple *) nit.cur,
                                        (BtorBitVectorTuple *) cnit.cur));
        (void) btor_next_hash_table_iterator (&nit);
        (void) btor_next_hash_table_iterator (&cnit);
      }
      assert (!btor_has_next_hash_table_iterator (&cnit));
      BTOR_CHKCLONE_EXPID (btor_next_node_hash_table_iterator (&it),
                           btor_next_node_hash_table_iterator (&cit));
    }
    assert (!btor_has_next_node_hash_table_iterator (&cit));
  }
  else
    assert (!btor->clone->fun_model);
}

void
btor_chkclone_sort (const BtorSort *sort, const BtorSort *clone)
{
  assert (sort->id == clone->id);
  assert (sort->kind == clone->kind);
  assert (sort->refs == clone->refs);
  assert (sort->ext_refs == clone->ext_refs);
  assert (sort->parents == clone->parents);

  unsigned i;

  switch (sort->kind)
  {
    case BTOR_BITVEC_SORT:
      assert (sort->bitvec.width == clone->bitvec.width);
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

#define BTOR_CHKCLONE_SLV_STATS(solver, csolver, field)   \
  do                                                      \
  {                                                       \
    assert (csolver->stats.field == solver->stats.field); \
  } while (0)

void
btor_chkclone_slv (Btor *btor)
{
  int i, h = btor->options.just_heuristic.val;

  assert ((!btor->slv && !btor->clone->slv) || (btor->slv && btor->clone->slv));
  if (!btor->slv) return;
  assert (btor->slv->kind == btor->clone->slv->kind);

  if (btor->slv->kind == BTOR_CORE_SOLVER_KIND)
  {
    BtorCoreSolver *slv  = BTOR_CORE_SOLVER (btor);
    BtorCoreSolver *cslv = BTOR_CORE_SOLVER (btor->clone);
    BtorHashTableIterator it;
    BtorHashTableIterator cit;

    BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (slv->lemmas, cslv->lemmas);

    if (slv->score)
    {
      assert (cslv->score);
      assert (slv->score->size == cslv->score->size);
      assert (slv->score->count == cslv->score->count);
      assert (slv->score->hash == cslv->score->hash);
      assert (slv->score->cmp == cslv->score->cmp);
      assert (!slv->score->first || cslv->score->first);
      if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
      {
        btor_init_node_hash_table_iterator (&it, slv->score);
        btor_init_node_hash_table_iterator (&cit, cslv->score);
        while (btor_has_next_node_hash_table_iterator (&it))
        {
          assert (btor_has_next_node_hash_table_iterator (&cit));
          BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (
              (BtorPtrHashTable *) it.bucket->data.asPtr,
              (BtorPtrHashTable *) cit.bucket->data.asPtr);
          BTOR_CHKCLONE_EXPID (btor_next_node_hash_table_iterator (&it),
                               btor_next_node_hash_table_iterator (&cit));
        }
        assert (!btor_has_next_node_hash_table_iterator (&cit));
      }
      else
      {
        assert (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP);
        // TODO check data as int
        BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (slv->score, cslv->score);
      }
    }
    else
    {
      assert (!cslv->score);
    }

    assert (BTOR_COUNT_STACK (slv->stats.lemmas_size)
            == BTOR_COUNT_STACK (cslv->stats.lemmas_size));
    for (i = 0; i < BTOR_COUNT_STACK (slv->stats.lemmas_size); i++)
      assert (BTOR_PEEK_STACK (slv->stats.lemmas_size, i)
              == BTOR_PEEK_STACK (cslv->stats.lemmas_size, i));

    BTOR_CHKCLONE_SLV_STATS (slv, cslv, lod_refinements);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, refinement_iterations);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, function_congruence_conflicts);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, beta_reduction_conflicts);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, extensionality_lemmas);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, lemmas_size_sum);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_failed_vars);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_assumed_vars);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_failed_applies);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_assumed_applies);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, eval_exp_calls);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, propagations);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, propagations_down);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, partial_beta_reduction_restarts);
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
  BTOR_CHKCLONE_AIG_ID_TABLE (
      btor_get_aig_mgr_aigvec_mgr (btor->avmgr)->id2aig,
      btor_get_aig_mgr_aigvec_mgr (btor->clone->avmgr)->id2aig);
  BTOR_CHKCLONE_AIG_CNF_ID_TABLE (
      btor_get_aig_mgr_aigvec_mgr (btor->avmgr)->cnfid2aig,
      btor_get_aig_mgr_aigvec_mgr (btor->clone->avmgr)->cnfid2aig);
  BTOR_CHKCLONE_NODE_ID_TABLE (btor->nodes_id_table,
                               btor->clone->nodes_id_table);
  BTOR_CHKCLONE_NODE_UNIQUE_TABLE (btor->nodes_unique_table,
                                   btor->clone->nodes_unique_table);
  BTOR_CHKCLONE_NODE_PTR_STACK (btor->functions_with_model,
                                btor->clone->functions_with_model);
  btor_chkclone_tables (btor);

  btor_chkclone_slv (btor);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

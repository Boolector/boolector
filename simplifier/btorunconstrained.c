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

#include "simplifier/btorunconstrained.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btormsg.h"
#include "utils/btorinthash.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

static bool
is_uc_write (Btor *btor, BtorNode *cond)
{
  assert (BTOR_IS_REGULAR_NODE (cond));
  assert (BTOR_IS_BV_COND_NODE (cond));
  assert (cond->parameterized);

  BtorNode *param, *nonparam, *cond_c, *cond_if, *cond_else;
  BtorParameterizedIterator it;

  cond_c    = cond->e[0];
  cond_if   = cond->e[1];
  cond_else = cond->e[2];

  if (BTOR_IS_INVERTED_NODE (cond_c) || !BTOR_IS_BV_EQ_NODE (cond_c)
      || !cond_c->parameterized)
    return false;

  if (BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (cond_if))
      && BTOR_REAL_ADDR_NODE (cond_if)->parameterized)
    return false;

  if (!BTOR_IS_INVERTED_NODE (cond_c->e[0])
      && BTOR_IS_PARAM_NODE (cond_c->e[0]))
  {
    param    = cond_c->e[0];
    nonparam = cond_c->e[1];
  }
  else if (!BTOR_IS_INVERTED_NODE (cond_c->e[1])
           && BTOR_IS_PARAM_NODE (cond_c->e[1]))
  {
    param    = cond_c->e[1];
    nonparam = cond_c->e[0];
  }
  else
    return false;

  if (BTOR_REAL_ADDR_NODE (nonparam)->parameterized) return false;

  btor_init_parameterized_iterator (&it, btor, cond_else);
  assert (btor_has_next_parameterized_iterator (&it));
  return param == btor_next_parameterized_iterator (&it)
         && !btor_has_next_parameterized_iterator (&it);
}

static void
mark_uc (Btor *btor, BtorIntHashTable *uc, BtorNode *exp)
{
  assert (BTOR_IS_REGULAR_NODE (exp));
  /* no inputs allowed here */
  assert (exp->arity > 0);

  BtorNode *subst;

  assert (!btor_contains_int_hash_table (uc, exp->id));
  btor_add_int_hash_table (uc, exp->id);

  BTOR_MSG (btor->msg,
            2,
            "found uc (%c) term %s",
            exp->parameterized ? 'p' : 'n',
            node2string (exp));

  if (exp->parameterized)
  {
    btor->stats.param_uc_props++;
    return;
  }

  if (BTOR_IS_APPLY_NODE (exp) || BTOR_IS_LAMBDA_NODE (exp)
      || BTOR_IS_FEQ_NODE (exp))
    btor->stats.fun_uc_props++;
  else
    btor->stats.bv_uc_props++;

  if (BTOR_IS_LAMBDA_NODE (exp) || BTOR_IS_FUN_COND_NODE (exp))
  {
    subst           = btor_uf_exp (btor, exp->sort_id, 0);
    subst->is_array = exp->is_array;
  }
  else
    subst = btor_aux_var_exp (btor, btor_get_exp_width (btor, exp));

  btor_insert_substitution (btor, exp, subst, 0);
  btor_release_exp (btor, subst);
}

void
btor_optimize_unconstrained (Btor *btor)
{
  assert (btor);
  assert (btor->options.rewrite_level.val > 2);
  assert (!btor->options.incremental.val);
  assert (!btor->options.model_gen.val);
  assert (check_id_table_mark_unset_dbg (btor));

  double start, delta;
  unsigned num_ucs;
  int i;
  bool isuc, uc[3], ucp[3];
  BtorNode *cur, *cur_parent, *lambda, *param;
  BtorNodePtrStack stack, roots;
  BtorHashTableIterator it;
  BtorNodeIterator pit;
  BtorParameterizedIterator parit;
  BtorMemMgr *mm;
  BtorIntHashTable *ucs;  /* unconstrained candidate nodes */
  BtorIntHashTable *ucsp; /* parameterized unconstrained candidate nodes */
  start = btor_time_stamp ();

  if (btor->bv_vars->count == 0 && btor->ufs->count == 0) return;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (roots);

  ucs  = btor_new_int_hash_table (mm);
  ucsp = btor_new_int_hash_table (mm);
  btor_init_substitutions (btor);

  /* collect nodes that might contribute to a unconstrained candidate
   * propagation */
  btor_init_node_hash_table_iterator (&it, btor->bv_vars);
  btor_queue_hash_table_iterator (&it, btor->ufs);
  while (btor_has_next_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->parents == 1)
    {
      cur_parent = BTOR_REAL_ADDR_NODE (cur->first_parent);
      btor_add_int_hash_table (ucs, cur->id);
      BTOR_MSG (btor->msg, 2, "found uc input %s", node2string (cur));
      // TODO (ma): why not just collect ufs and vars?
      if (BTOR_IS_UF_NODE (cur)
          || (cur_parent->kind != BTOR_ARGS_NODE
              && cur_parent->kind != BTOR_LAMBDA_NODE))
        BTOR_PUSH_STACK (mm, stack, cur_parent);
    }
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->mark == 0)
    {
      cur->mark = 1;
      if (!cur->parents)
        BTOR_PUSH_STACK (mm, roots, cur);
      else
      {
        btor_init_parent_iterator (&pit, cur);
        while (btor_has_next_parent_iterator (&pit))
          BTOR_PUSH_STACK (mm, stack, btor_next_parent_iterator (&pit));
      }
    }
  }

  /* identify unconstrained candidates */
  for (i = 0; i < BTOR_COUNT_STACK (roots); i++)
    BTOR_PUSH_STACK (mm, stack, BTOR_PEEK_STACK (roots, i));
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (!cur->mark) continue;

    assert (!BTOR_IS_BV_CONST_NODE (cur));
    assert (!BTOR_IS_BV_VAR_NODE (cur));
    assert (!BTOR_IS_UF_NODE (cur));
    assert (!BTOR_IS_PARAM_NODE (cur));

    if (cur->mark == 1)
    {
      cur->mark = 2;
      BTOR_PUSH_STACK (mm, stack, cur);
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_NODE (cur->e[i]));
    }
    else
    {
      assert (cur->mark == 2);
      cur->mark = 0;

      /* check if parameterized term can be unconstrained */
      isuc = true;
      btor_init_parameterized_iterator (&parit, btor, cur);
      while (btor_has_next_parameterized_iterator (&parit))
      {
        /* parameterized expressions are only unconstrained if they
         * are instantiated once in case full beta reduction is
         * applied. */
        param = btor_next_parameterized_iterator (&parit);
        assert (BTOR_IS_REGULAR_NODE (param));
        assert (BTOR_IS_PARAM_NODE (param));
        assert (btor_param_is_bound (param));
        lambda = btor_param_get_binding_lambda (param);
        assert (lambda);
        /* get head lambda of function */
        while (
            lambda->parents == 1
            && BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (lambda->first_parent)))
        {
          assert (BTOR_IS_LAMBDA_NODE (lambda));
          lambda = BTOR_REAL_ADDR_NODE (lambda->first_parent);
        }
        assert (BTOR_IS_LAMBDA_NODE (lambda));
        if (lambda->parents > 1)
        {
          isuc = false;
          break;
        }
      }
      if (!isuc) continue;

      /* propagate unconstrained candidates */
      if (cur->parents == 0 || (cur->parents == 1 && !cur->constraint))
      {
        for (i = 0; i < cur->arity; i++)
        {
          uc[i] = btor_contains_int_hash_table (
              ucs, BTOR_REAL_ADDR_NODE (cur->e[i])->id);
          ucp[i] = btor_contains_int_hash_table (
              ucsp, BTOR_REAL_ADDR_NODE (cur->e[i])->id);
          assert (!uc[i] || uc[i] != ucp[i]);
          assert (!ucp[i] || uc[i] != ucp[i]);
          assert (!ucp[i] || cur->parameterized || BTOR_IS_LAMBDA_NODE (cur));
        }

        switch (cur->kind)
        {
          case BTOR_SLICE_NODE:
          case BTOR_APPLY_NODE:
            if (uc[0])
            {
              if (cur->parameterized)
              {
                if (BTOR_IS_APPLY_NODE (cur)) mark_uc (btor, ucsp, cur);
              }
              else
                mark_uc (btor, ucs, cur);
            }
            break;
          case BTOR_ADD_NODE:
          case BTOR_BEQ_NODE:
          case BTOR_FEQ_NODE:
            if (!cur->parameterized && (uc[0] || uc[1]))
              mark_uc (btor, ucs, cur);
            break;
          case BTOR_ULT_NODE:
          case BTOR_CONCAT_NODE:
          case BTOR_AND_NODE:
          case BTOR_MUL_NODE:
          case BTOR_SLL_NODE:
          case BTOR_SRL_NODE:
          case BTOR_UDIV_NODE:
          case BTOR_UREM_NODE:
            if (!cur->parameterized && uc[0] && uc[1]) mark_uc (btor, ucs, cur);
            break;
          case BTOR_BCOND_NODE:
            if ((uc[1] && uc[2]) || (uc[0] && (uc[1] || uc[2])))
              mark_uc (btor, ucs, cur);
            else if (uc[1] && ucp[2])
            {
              /* case: x = t ? uc : ucp */
              if (is_uc_write (btor, cur)) mark_uc (btor, ucsp, cur);
            }
            break;
          // TODO (ma): functions with parents > 1 can still be
          //            handled as unconstrained, but the applications
          //            on it cannot be unconstrained anymore
          //            (function congruence needs to be enforced)
          case BTOR_LAMBDA_NODE:
            assert (cur->parents <= 1);
            if (ucp[1]
                /* only consider head lambda of curried lambdas */
                && (!cur->first_parent
                    || !BTOR_IS_LAMBDA_NODE (
                           BTOR_REAL_ADDR_NODE (cur->first_parent))))
              mark_uc (btor, ucs, cur);
            break;
          default: break;
        }
      }
    }
  }

  num_ucs = btor->substitutions->count;
  btor_substitute_and_rebuild (btor, btor->substitutions, 0);

  /* cleanup */
  btor_delete_substitutions (btor);
  btor_free_int_hash_table (ucs);
  btor_free_int_hash_table (ucsp);
  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, roots);

  delta = btor_time_stamp () - start;
  btor->time.ucopt += delta;
  BTOR_MSG (btor->msg,
            1,
            "detected %u unconstrained terms in %.3f seconds",
            num_ucs,
            delta);
}

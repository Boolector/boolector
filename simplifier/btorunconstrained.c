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
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

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
  int i, uc[3], isuc;
  BtorNode *cur, *cur_parent, *subst, *lambda, *param;
  BtorNodePtrStack stack, roots;
  BtorPtrHashTable *ucs; /* unconstrained (candidate) nodes */
  BtorHashTableIterator it;
  BtorNodeIterator pit;
  BtorParameterizedIterator parit;
  BtorMemMgr *mm;

  start = btor_time_stamp ();

  if (btor->bv_vars->count == 0 && btor->ufs->count == 0) return;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (roots);

  ucs = btor_new_ptr_hash_table (mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
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
      assert (!btor_find_in_ptr_hash_table (ucs, cur));
      btor_insert_in_ptr_hash_table (ucs, btor_copy_exp (btor, cur));
      BTOR_MSG (
          btor->msg, 2, "found unconstrained input %s", node2string (cur));
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
      isuc = 1;
      btor_init_parameterized_iterator (&parit, btor, cur);
      while (btor_has_next_parameterized_iterator (&parit))
      {
        /* parameterized expressions are possibly unconstrained if the
         * lambda(s) parameterizing it do not have more than 1 parent */
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
          isuc = 0;
          break;
        }
      }
      if (!isuc) continue;

      /* propagate unconstrained candidates */
      if (cur->parents == 0 || (cur->parents == 1 && !cur->constraint))
      {
        for (i = cur->arity - 1; i >= 0; i--)
          uc[i] = (btor_find_in_ptr_hash_table (
                      ucs, BTOR_REAL_ADDR_NODE (cur->e[i])))
                      ? 1
                      : 0;

        switch (cur->kind)
        {
          case BTOR_SLICE_NODE:
          case BTOR_APPLY_NODE:
            if (uc[0])
            {
              if (BTOR_IS_SLICE_NODE (cur))
                btor->stats.bv_uc_props++;
              else
                btor->stats.fun_uc_props++;
              btor_insert_in_ptr_hash_table (ucs, btor_copy_exp (btor, cur));
              subst = btor_aux_var_exp (btor, btor_get_exp_width (btor, cur));
              BTOR_MSG (btor->msg,
                        2,
                        "found unconstrained term %s",
                        node2string (cur));
              btor_insert_substitution (btor, cur, subst, 0);
              btor_release_exp (btor, subst);
            }
            break;
          case BTOR_ADD_NODE:
          case BTOR_BEQ_NODE:
          case BTOR_FEQ_NODE:
            if (uc[0] || uc[1])
            {
              if (BTOR_IS_ADD_NODE (cur) || BTOR_IS_BV_EQ_NODE (cur))
                btor->stats.bv_uc_props++;
              else
                btor->stats.fun_uc_props++;
              btor_insert_in_ptr_hash_table (ucs, btor_copy_exp (btor, cur));
              subst = btor_aux_var_exp (btor, btor_get_exp_width (btor, cur));
              BTOR_MSG (btor->msg,
                        2,
                        "found unconstrained term %s",
                        node2string (cur));
              btor_insert_substitution (btor, cur, subst, 0);
              btor_release_exp (btor, subst);
            }
            break;
          case BTOR_ULT_NODE:
          case BTOR_CONCAT_NODE:
          case BTOR_AND_NODE:
          case BTOR_MUL_NODE:
          case BTOR_SLL_NODE:
          case BTOR_SRL_NODE:
          case BTOR_UDIV_NODE:
          case BTOR_UREM_NODE:
            if (uc[0] && uc[1])
            {
              btor->stats.bv_uc_props++;
              btor_insert_in_ptr_hash_table (ucs, btor_copy_exp (btor, cur));
              subst = btor_aux_var_exp (btor, btor_get_exp_width (btor, cur));
              BTOR_MSG (btor->msg,
                        2,
                        "found unconstrained term %s",
                        node2string (cur));
              btor_insert_substitution (btor, cur, subst, 0);
              btor_release_exp (btor, subst);
            }
            break;
          case BTOR_BCOND_NODE:
            if ((uc[1] && uc[2]) || (uc[0] && (uc[1] || uc[2])))
            {
              btor->stats.bv_uc_props++;
              btor_insert_in_ptr_hash_table (ucs, btor_copy_exp (btor, cur));
              subst = btor_aux_var_exp (btor, btor_get_exp_width (btor, cur));
              BTOR_MSG (btor->msg,
                        2,
                        "found unconstrained term %s",
                        node2string (cur));
              btor_insert_substitution (btor, cur, subst, 0);
              btor_release_exp (btor, subst);
            }
            break;
          case BTOR_LAMBDA_NODE:
            assert (cur->parents <= 1);
            if (uc[1]
                /* only consider head lambda of curried lambdas */
                && (!cur->first_parent
                    || !BTOR_IS_LAMBDA_NODE (
                           BTOR_REAL_ADDR_NODE (cur->first_parent))))
            {
              btor->stats.fun_uc_props++;
              btor_insert_in_ptr_hash_table (ucs, btor_copy_exp (btor, cur));
              subst = btor_uf_exp (btor, cur->sort_id, 0);
              BTOR_MSG (btor->msg,
                        2,
                        "found unconstrained term %s",
                        node2string (cur));
              btor_insert_substitution (btor, cur, subst, 0);
              btor_release_exp (btor, subst);
            }
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
  btor_init_hash_table_iterator (&it, ucs);
  while (btor_has_next_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (ucs);

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

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

#include "simplifier/btorunconstrained.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btormsg.h"
#include "utils/btorhashint.h"
#include "utils/btormisc.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

static bool
is_uc_write (BtorNode *cond)
{
  assert (BTOR_IS_REGULAR_NODE (cond));
  assert (btor_is_bv_cond_node (cond));
  assert (cond->parameterized);

  BtorNode *lambda;

  if (cond->parents != 1) return false;

  lambda = BTOR_REAL_ADDR_NODE (cond->first_parent);
  if (!btor_is_lambda_node (lambda)) return false;

  return btor_lambda_get_static_rho (lambda) != 0;
}

static void
mark_uc (Btor *btor, BtorIntHashTable *uc, BtorNode *exp)
{
  assert (BTOR_IS_REGULAR_NODE (exp));
  /* no inputs allowed here */
  assert (exp->arity > 0);

  BtorNode *subst;

  assert (!btor_hashint_table_contains (uc, exp->id));
  btor_hashint_table_add (uc, exp->id);

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

  if (btor_is_apply_node (exp) || btor_is_lambda_node (exp)
      || btor_is_fun_eq_node (exp))
    btor->stats.fun_uc_props++;
  else
    btor->stats.bv_uc_props++;

  if (btor_is_lambda_node (exp) || btor_is_fun_cond_node (exp))
  {
    subst           = btor_uf_exp (btor, btor_exp_get_sort_id (exp), 0);
    subst->is_array = exp->is_array;
  }
  else
    subst = btor_var_exp (btor, btor_exp_get_sort_id (exp), 0);

  btor_insert_substitution (btor, exp, subst, 0);
  btor_release_exp (btor, subst);
}

void
btor_optimize_unconstrained (Btor *btor)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2);
  assert (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
  assert (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN));

  double start, delta;
  unsigned num_ucs;
  int i;
  bool uc[3], ucp[3];
  BtorNode *cur, *cur_parent;
  BtorNodePtrStack stack, roots;
  BtorPtrHashTableIterator it;
  BtorNodeIterator pit;
  BtorMemMgr *mm;
  BtorIntHashTable *ucs;  /* unconstrained candidate nodes */
  BtorIntHashTable *ucsp; /* parameterized unconstrained candidate nodes */
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  if (btor->bv_vars->count == 0 && btor->ufs->count == 0) return;

  start = btor_time_stamp ();
  mm    = btor->mm;
  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, roots);
  uc[0] = uc[1] = uc[2] = ucp[0] = ucp[1] = ucp[2] = false;

  mark = btor_hashint_map_new (mm);
  ucs  = btor_hashint_table_new (mm);
  ucsp = btor_hashint_table_new (mm);
  btor_init_substitutions (btor);

  /* collect nodes that might contribute to a unconstrained candidate
   * propagation */
  btor_iter_hashptr_init (&it, btor->bv_vars);
  btor_iter_hashptr_queue (&it, btor->ufs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->parents == 1)
    {
      cur_parent = BTOR_REAL_ADDR_NODE (cur->first_parent);
      btor_hashint_table_add (ucs, cur->id);
      BTOR_MSG (btor->msg, 2, "found uc input %s", node2string (cur));
      // TODO (ma): why not just collect ufs and vars?
      if (btor_is_uf_node (cur)
          || (cur_parent->kind != BTOR_ARGS_NODE
              && cur_parent->kind != BTOR_LAMBDA_NODE))
        BTOR_PUSH_STACK (stack, cur_parent);
    }
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (!btor_hashint_map_contains (mark, cur->id))
    {
      btor_hashint_map_add (mark, cur->id);
      if (!cur->parents)
        BTOR_PUSH_STACK (roots, cur);
      else
      {
        btor_init_parent_iterator (&pit, cur);
        while (btor_has_next_parent_iterator (&pit))
          BTOR_PUSH_STACK (stack, btor_next_parent_iterator (&pit));
      }
    }
  }

  /* identify unconstrained candidates */
  for (i = 0; i < BTOR_COUNT_STACK (roots); i++)
    BTOR_PUSH_STACK (stack, BTOR_PEEK_STACK (roots, i));
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    d = btor_hashint_map_get (mark, cur->id);

    if (!d) continue;

    assert (!btor_is_bv_const_node (cur));
    assert (!btor_is_bv_var_node (cur));
    assert (!btor_is_uf_node (cur));
    assert (!btor_is_param_node (cur));

    if (d->as_int == 0)
    {
      d->as_int = 1;
      BTOR_PUSH_STACK (stack, cur);
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (stack, BTOR_REAL_ADDR_NODE (cur->e[i]));
    }
    else
    {
      assert (d->as_int == 1);
      btor_hashint_map_remove (mark, cur->id, 0);

      /* propagate unconstrained candidates */
      if (cur->parents == 0 || (cur->parents == 1 && !cur->constraint))
      {
        for (i = 0; i < cur->arity; i++)
        {
          uc[i] = btor_hashint_table_contains (
              ucs, BTOR_REAL_ADDR_NODE (cur->e[i])->id);
          ucp[i] = btor_hashint_table_contains (
              ucsp, BTOR_REAL_ADDR_NODE (cur->e[i])->id);
          assert (!uc[i] || uc[i] != ucp[i]);
          assert (!ucp[i] || uc[i] != ucp[i]);
          assert (!ucp[i] || cur->parameterized || btor_is_lambda_node (cur));
        }

        switch (cur->kind)
        {
          case BTOR_SLICE_NODE:
          case BTOR_APPLY_NODE:
            if (uc[0])
            {
              if (cur->parameterized)
              {
                if (btor_is_apply_node (cur)) mark_uc (btor, ucsp, cur);
              }
              else
                mark_uc (btor, ucs, cur);
            }
            break;
          case BTOR_ADD_NODE:
          case BTOR_BV_EQ_NODE:
          case BTOR_FUN_EQ_NODE:
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
          case BTOR_COND_NODE:
            if ((uc[1] && uc[2]) || (uc[0] && (uc[1] || uc[2])))
              mark_uc (btor, ucs, cur);
            else if (uc[1] && ucp[2])
            {
              /* case: x = t ? uc : ucp */
              if (is_uc_write (cur)) mark_uc (btor, ucsp, cur);
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
                    || !btor_is_lambda_node (cur->first_parent)))
              mark_uc (btor, ucs, cur);
            break;
          default: break;
        }
      }
    }
  }
  btor_hashint_map_delete (mark);

  num_ucs = btor->substitutions->count;
  btor_substitute_and_rebuild (btor, btor->substitutions);

  /* cleanup */
  btor_delete_substitutions (btor);
  btor_hashint_table_delete (ucs);
  btor_hashint_table_delete (ucsp);
  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (roots);

  delta = btor_time_stamp () - start;
  btor->time.ucopt += delta;
  BTOR_MSG (btor->msg,
            1,
            "detected %u unconstrained terms in %.3f seconds",
            num_ucs,
            delta);
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorunconstrained.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorexp.h"
#include "btormsg.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

static bool
is_uc_write (BtorNode *cond)
{
  assert (btor_node_is_regular (cond));
  assert (btor_node_is_bv_cond (cond));
  assert (cond->parameterized);

  BtorNode *lambda;

  if (cond->parents != 1) return false;

  lambda = btor_node_real_addr (cond->first_parent);
  if (!btor_node_is_lambda (lambda)) return false;

  return btor_node_lambda_get_static_rho (lambda) != 0;
}

static void
mark_uc (Btor *btor, BtorIntHashTable *uc, BtorNode *exp)
{
  assert (btor_node_is_regular (exp));
  /* no inputs allowed here */
  assert (exp->arity > 0);

  BtorNode *subst;

  assert (!btor_hashint_table_contains (uc, exp->id));
  btor_hashint_table_add (uc, exp->id);

  BTOR_MSG (btor->msg,
            2,
            "found uc (%c) term %s",
            exp->parameterized ? 'p' : 'n',
            btor_util_node2string (exp));

  if (exp->parameterized)
  {
    btor->stats.param_uc_props++;
    return;
  }

  if (btor_node_is_apply (exp) || btor_node_is_lambda (exp)
      || btor_node_is_fun_eq (exp) || btor_node_is_update (exp))
    btor->stats.fun_uc_props++;
  else
    btor->stats.bv_uc_props++;

  if (btor_node_is_lambda (exp) || btor_node_is_fun_cond (exp)
      || btor_node_is_update (exp))
  {
    subst           = btor_exp_uf (btor, btor_node_get_sort_id (exp), 0);
    subst->is_array = exp->is_array;
  }
  else
    subst = btor_exp_var (btor, btor_node_get_sort_id (exp), 0);

  btor_insert_substitution (btor, exp, subst, false);
  btor_node_release (btor, subst);
}

void
btor_optimize_unconstrained (Btor *btor)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2);
  assert (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
  assert (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN));

  double start, delta;
  uint32_t i, num_ucs;
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

  start = btor_util_time_stamp ();
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
    assert (btor_node_is_regular (cur));
    if (cur->parents == 1)
    {
      cur_parent = btor_node_real_addr (cur->first_parent);
      btor_hashint_table_add (ucs, cur->id);
      BTOR_MSG (btor->msg, 2, "found uc input %s", btor_util_node2string (cur));
      // TODO (ma): why not just collect ufs and vars?
      if (btor_node_is_uf (cur)
          || (cur_parent->kind != BTOR_ARGS_NODE
              && cur_parent->kind != BTOR_LAMBDA_NODE))
        BTOR_PUSH_STACK (stack, cur_parent);
    }
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (btor_node_is_regular (cur));
    if (!btor_hashint_map_contains (mark, cur->id))
    {
      btor_hashint_map_add (mark, cur->id);
      if (!cur->parents)
        BTOR_PUSH_STACK (roots, cur);
      else
      {
        btor_iter_parent_init (&pit, cur);
        while (btor_iter_parent_has_next (&pit))
          BTOR_PUSH_STACK (stack, btor_iter_parent_next (&pit));
      }
    }
  }

  /* identify unconstrained candidates */
  for (i = 0; i < BTOR_COUNT_STACK (roots); i++)
    BTOR_PUSH_STACK (stack, BTOR_PEEK_STACK (roots, i));
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (btor_node_is_regular (cur));
    d = btor_hashint_map_get (mark, cur->id);

    if (!d) continue;

    assert (!btor_node_is_bv_const (cur));
    assert (!btor_node_is_bv_var (cur));
    assert (!btor_node_is_uf (cur));
    assert (!btor_node_is_param (cur));

    if (d->as_int == 0)
    {
      d->as_int = 1;
      BTOR_PUSH_STACK (stack, cur);
      for (i = 1; i <= cur->arity; i++)
        BTOR_PUSH_STACK (stack, btor_node_real_addr (cur->e[cur->arity - i]));
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
              ucs, btor_node_real_addr (cur->e[i])->id);
          ucp[i] = btor_hashint_table_contains (
              ucsp, btor_node_real_addr (cur->e[i])->id);
          assert (!uc[i] || uc[i] != ucp[i]);
          assert (!ucp[i] || uc[i] != ucp[i]);
          assert (!ucp[i] || cur->parameterized || btor_node_is_lambda (cur));
        }

        switch (cur->kind)
        {
          case BTOR_BV_SLICE_NODE:
          case BTOR_APPLY_NODE:
            if (uc[0])
            {
              if (cur->parameterized)
              {
                if (btor_node_is_apply (cur)) mark_uc (btor, ucsp, cur);
              }
              else
                mark_uc (btor, ucs, cur);
            }
            break;
          case BTOR_BV_ADD_NODE:
          case BTOR_BV_EQ_NODE:
          case BTOR_FUN_EQ_NODE:
            if (!cur->parameterized && (uc[0] || uc[1]))
              mark_uc (btor, ucs, cur);
            break;
          case BTOR_BV_ULT_NODE:
          case BTOR_BV_CONCAT_NODE:
          case BTOR_BV_AND_NODE:
          case BTOR_BV_MUL_NODE:
          case BTOR_BV_SLL_NODE:
          case BTOR_BV_SRL_NODE:
          case BTOR_BV_UDIV_NODE:
          case BTOR_BV_UREM_NODE:
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
          case BTOR_UPDATE_NODE:
            if (uc[0] && uc[2]) mark_uc (btor, ucs, cur);
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
                    || !btor_node_is_lambda (cur->first_parent)))
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

  delta = btor_util_time_stamp () - start;
  btor->time.ucopt += delta;
  BTOR_MSG (btor->msg,
            1,
            "detected %u unconstrained terms in %.3f seconds",
            num_ucs,
            delta);
}

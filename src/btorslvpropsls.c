/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvpropsls.h"

#include "utils/btoriter.h"
#include "utils/btorutil.h"

#include "btorslvsls.h"  // FIXME remove

void
btor_propsls_update_cone (Btor *btor,
                          BtorIntHashTable *roots,
                          BtorPtrHashTable *score,
                          BtorIntHashTable *exps,
                          BtorBitVector *assignment,
                          uint64_t *stats_updates,
                          double *time_update_cone,
                          double *time_update_cone_reset,
                          double *time_update_cone_model_gen,
                          double *time_update_cone_compute_score)
{
  assert (btor);
  assert (roots);
  assert (exps);
  assert (exps->count);
  assert (assignment);
  assert (time_update_cone);
  assert (time_update_cone_reset);
  assert (time_update_cone_model_gen);

  double start, delta;
  uint32_t i, j;
  BtorNode *exp, *cur;
  BtorNodeIterator nit;
  BtorPtrHashTable *bv_model;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, cone;
  BtorIntHashTable *cache;
  BtorBitVector *bv, *e[3];
  BtorMemMgr *mm;

  start = delta = btor_time_stamp ();

  mm       = btor->mm;
  bv_model = btor->bv_model;
  assert (bv_model);

#ifndef NDEBUG
  BtorHashTableIterator it;
  BtorNode *root;
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    if (btor_is_false_bv (btor_get_bv_model (btor, root)))
      assert (btor_contains_int_hash_map (roots, BTOR_GET_ID_NODE (root)));
    else
      assert (!btor_contains_int_hash_map (roots, BTOR_GET_ID_NODE (root)));
  }
#endif

  /* reset cone */
  BTOR_INIT_STACK (cone);
  BTOR_INIT_STACK (stack);
  for (i = 0; i < exps->size; i++)
  {
    if (!exps->keys[i]) continue;
    exp = btor_get_node_by_id (btor, exps->keys[i]);
    assert (BTOR_IS_REGULAR_NODE (exp));
    assert (btor_is_bv_var_node (exp));
    BTOR_PUSH_STACK (btor->mm, stack, exp);
  }
  cache = btor_new_int_hash_table (mm);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (btor_contains_int_hash_table (cache, cur->id)) continue;
    btor_add_int_hash_table (cache, cur->id);
    if (!btor_contains_int_hash_table (exps, cur->id))
      BTOR_PUSH_STACK (mm, cone, cur);
    *stats_updates += 1;

    // FIXME update score similarly to assignments
    // (individually, do not remove from hash table)
    //
    /* reset previous score */
    if (score)
    {
      if ((b = btor_get_ptr_hash_table (score, cur)))
        btor_remove_ptr_hash_table (score, cur, 0, 0);
      if ((b = btor_get_ptr_hash_table (score, BTOR_INVERT_NODE (cur))))
        btor_remove_ptr_hash_table (score, BTOR_INVERT_NODE (cur), 0, 0);
    }

    /* push parents */
    btor_init_parent_iterator (&nit, cur);
    while (btor_has_next_parent_iterator (&nit))
      BTOR_PUSH_STACK (mm, stack, btor_next_parent_iterator (&nit));
  }
  BTOR_RELEASE_STACK (mm, stack);
  btor_delete_int_hash_table (cache);

  *time_update_cone_reset += btor_time_stamp () - delta;
  delta = btor_time_stamp ();

  /* update assignment of exps */
  for (i = 0; i < exps->size; i++)
  {
    if (!exps->keys[i]) continue;
    exp = btor_get_node_by_id (btor, exps->keys[i]);
    b   = btor_get_ptr_hash_table (bv_model, exp);
    assert (b);
    if ((exp->constraint || btor_get_ptr_hash_table (btor->assumptions, exp)
         || btor_get_ptr_hash_table (btor->assumptions, BTOR_INVERT_NODE (exp)))
        && btor_compare_bv (b->data.as_ptr, assignment))
    {
      /* old assignment != new assignment */
      btor_propsls_update_roots (btor, roots, exp, assignment);
    }
    btor_free_bv (mm, b->data.as_ptr);
    b->data.as_ptr = btor_copy_bv (mm, assignment);
    if ((b = btor_get_ptr_hash_table (bv_model, BTOR_INVERT_NODE (exp))))
    {
      btor_free_bv (mm, b->data.as_ptr);
      b->data.as_ptr = btor_not_bv (mm, assignment);
    }
  }

  /* update cone */
  qsort (cone.start,
         BTOR_COUNT_STACK (cone),
         sizeof (BtorNode *),
         btor_compare_exp_by_id_qsort_asc);
  for (i = 0; i < BTOR_COUNT_STACK (cone); i++)
  {
    cur = BTOR_PEEK_STACK (cone, i);
    assert (BTOR_IS_REGULAR_NODE (cur));
    for (j = 0; j < cur->arity; j++)
    {
      if (btor_is_bv_const_node (cur->e[j]))
      {
        e[j] = BTOR_IS_INVERTED_NODE (cur->e[j])
                   ? btor_copy_bv (mm, btor_const_get_invbits (cur->e[j]))
                   : btor_copy_bv (mm, btor_const_get_bits (cur->e[j]));
      }
      else
      {
        b = btor_get_ptr_hash_table (bv_model, BTOR_REAL_ADDR_NODE (cur->e[j]));
        /* Note: generate model enabled branch for ite (and does not
         * generate model for nodes in the branch, hence !b may happen */
        if (!b)
          e[j] = btor_recursively_compute_assignment (
              btor, bv_model, btor->fun_model, cur->e[j]);
        else
          e[j] = BTOR_IS_INVERTED_NODE (cur->e[j])
                     ? btor_not_bv (mm, b->data.as_ptr)
                     : btor_copy_bv (mm, b->data.as_ptr);
      }
    }
    switch (cur->kind)
    {
      case BTOR_ADD_NODE: bv = btor_add_bv (mm, e[0], e[1]); break;
      case BTOR_AND_NODE: bv = btor_and_bv (mm, e[0], e[1]); break;
      case BTOR_BV_EQ_NODE: bv = btor_eq_bv (mm, e[0], e[1]); break;
      case BTOR_ULT_NODE: bv = btor_ult_bv (mm, e[0], e[1]); break;
      case BTOR_SLL_NODE: bv = btor_sll_bv (mm, e[0], e[1]); break;
      case BTOR_SRL_NODE: bv = btor_srl_bv (mm, e[0], e[1]); break;
      case BTOR_MUL_NODE: bv = btor_mul_bv (mm, e[0], e[1]); break;
      case BTOR_UDIV_NODE: bv = btor_udiv_bv (mm, e[0], e[1]); break;
      case BTOR_UREM_NODE: bv = btor_urem_bv (mm, e[0], e[1]); break;
      case BTOR_CONCAT_NODE: bv = btor_concat_bv (mm, e[0], e[1]); break;
      case BTOR_SLICE_NODE:
        bv = btor_slice_bv (
            mm, e[0], btor_slice_get_upper (cur), btor_slice_get_lower (cur));
        break;
      default:
        assert (btor_is_cond_node (cur));
        bv = btor_is_true_bv (e[0]) ? btor_copy_bv (mm, e[1])
                                    : btor_copy_bv (mm, e[2]);
    }

    /* update assignment */

    b = btor_get_ptr_hash_table (bv_model, cur);

    /* update roots table */
    if (cur->constraint || btor_get_ptr_hash_table (btor->assumptions, cur)
        || btor_get_ptr_hash_table (btor->assumptions, BTOR_INVERT_NODE (cur)))
    {
      assert (b); /* must be contained, is root */
      /* old assignment != new assignment */
      if (btor_compare_bv (b->data.as_ptr, bv))
        btor_propsls_update_roots (btor, roots, cur, bv);
    }

    /* update assignments */
    /* Note: generate model enabled branch for ite (and does not generate
     *       model for nodes in the branch, hence !b may happen */
    if (!b)
    {
      b = btor_add_ptr_hash_table (bv_model, btor_copy_exp (btor, cur));
      b->data.as_ptr = bv;
    }
    else
    {
      btor_free_bv (mm, b->data.as_ptr);
      b->data.as_ptr = bv;
    }

    if ((b = btor_get_ptr_hash_table (bv_model, BTOR_INVERT_NODE (cur))))
    {
      btor_free_bv (mm, b->data.as_ptr);
      b->data.as_ptr = btor_not_bv (mm, bv);
    }
    /* cleanup */
    for (j = 0; j < cur->arity; j++) btor_free_bv (mm, e[j]);
  }
  BTOR_RELEASE_STACK (mm, cone);
  *time_update_cone_model_gen += btor_time_stamp () - delta;

  if (score)
  {
    delta = btor_time_stamp ();
    btor_compute_sls_scores (btor, score);
    *time_update_cone_compute_score += btor_time_stamp () - delta;
  }

#ifndef NDEBUG
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    if (btor_is_false_bv (btor_get_bv_model (btor, root)))
      assert (btor_contains_int_hash_map (roots, BTOR_GET_ID_NODE (root)));
    else
      assert (!btor_contains_int_hash_map (roots, BTOR_GET_ID_NODE (root)));
  }
#endif
  *time_update_cone += btor_time_stamp () - start;
}

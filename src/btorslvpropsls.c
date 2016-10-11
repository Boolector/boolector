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

#include "btorprintmodel.h"
#include "utils/btorexpiter.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

static inline void
update_roots (Btor *btor,
              BtorIntHashTable *roots,
              BtorNode *exp,
              BtorBitVector *bv)
{
  assert (btor);
  assert (roots);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (bv);
  assert (btor_compare_bv (btor_get_bv_model (btor, exp), bv));

  (void) btor;

  /* exp: old assignment = 0, new assignment = 1 -> bv = 1
   *      -> remove */
  if (btor_get_int_hash_map (roots, exp->id))
  {
    btor_remove_int_hash_map (roots, exp->id, 0);
    assert (btor_is_false_bv (btor_get_bv_model (btor, exp)));
    assert (btor_is_true_bv (bv));
  }
  /* -exp: old assignment = 0, new assignment = 1 -> bv = 0
   * -> remove */
  else if (btor_get_int_hash_map (roots, -exp->id))
  {
    btor_remove_int_hash_map (roots, -exp->id, 0);
    assert (
        btor_is_false_bv (btor_get_bv_model (btor, BTOR_INVERT_NODE (exp))));
    assert (btor_is_false_bv (bv));
  }
  /* exp: old assignment = 1, new assignment = 0 -> bv = 0
   * -> add */
  else if (btor_is_false_bv (bv))
  {
    btor_add_int_hash_map (roots, exp->id);
    assert (btor_is_true_bv (btor_get_bv_model (btor, exp)));
  }
  /* -exp: old assignment = 1, new assignment = 0 -> bv = 1
   * -> add */
  else
  {
    assert (btor_is_true_bv (bv));
    btor_add_int_hash_map (roots, -exp->id);
    assert (btor_is_true_bv (btor_get_bv_model (btor, BTOR_INVERT_NODE (exp))));
  }
}

void
btor_propsls_update_cone (Btor *btor,
                          BtorPtrHashTable *bv_model,
                          BtorIntHashTable *roots,
                          BtorPtrHashTable *score,
                          BtorIntHashTable *exps,
                          uint64_t *stats_updates,
                          double *time_update_cone,
                          double *time_update_cone_reset,
                          double *time_update_cone_model_gen,
                          double *time_update_cone_compute_score)
{
  assert (btor);
  assert (bv_model);
  assert (roots);
  assert (exps);
  assert (exps->count);
  assert (time_update_cone);
  assert (time_update_cone_reset);
  assert (time_update_cone_model_gen);

  double start, delta;
  uint32_t i, j;
  BtorNode *exp, *cur;
  BtorNodeIterator nit;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, cone;
  BtorIntHashTable *cache;
  BtorBitVector *bv, *e[3], *ass;
  BtorMemMgr *mm;

  start = delta = btor_time_stamp ();

  mm = btor->mm;

#ifndef NDEBUG
  BtorPtrHashTableIterator it;
  BtorNode *root;
  btor_init_ptr_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    root = btor_next_ptr_hash_table_iterator (&it);
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
    ass = (BtorBitVector *) exps->data[i].as_ptr;
    b   = btor_get_ptr_hash_table (bv_model, exp);
    assert (b);
    if ((exp->constraint || btor_get_ptr_hash_table (btor->assumptions, exp)
         || btor_get_ptr_hash_table (btor->assumptions, BTOR_INVERT_NODE (exp)))
        && btor_compare_bv (b->data.as_ptr, ass))
    {
      /* old assignment != new assignment */
      update_roots (btor, roots, exp, ass);
    }
    btor_free_bv (mm, b->data.as_ptr);
    b->data.as_ptr = btor_copy_bv (mm, ass);
    if ((b = btor_get_ptr_hash_table (bv_model, BTOR_INVERT_NODE (exp))))
    {
      btor_free_bv (mm, b->data.as_ptr);
      b->data.as_ptr = btor_not_bv (mm, ass);
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
        update_roots (btor, roots, cur, bv);
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
    btor_propsls_compute_sls_scores (
        btor, btor->bv_model, btor->fun_model, score);
    *time_update_cone_compute_score += btor_time_stamp () - delta;
  }

#ifndef NDEBUG
  btor_init_ptr_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    root = btor_next_ptr_hash_table_iterator (&it);
    if (btor_is_false_bv (btor_get_bv_model (btor, root)))
      assert (btor_contains_int_hash_map (roots, BTOR_GET_ID_NODE (root)));
    else
      assert (!btor_contains_int_hash_map (roots, BTOR_GET_ID_NODE (root)));
  }
#endif
  *time_update_cone += btor_time_stamp () - start;
}

/*------------------------------------------------------------------------*/

#define BTOR_SLS_SCORE_CFACT 0.5     /* same as in Z3 (c1) */
#define BTOR_SLS_SCORE_F_CFACT 0.025 /* same as in Z3 (c3) */

static int
hamming_distance (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int res;
  BtorBitVector *bv, *bvdec = 0, *zero, *ones, *tmp;

  zero = btor_new_bv (btor->mm, bv1->width);
  ones = btor_ones_bv (btor->mm, bv1->width);
  bv   = btor_xor_bv (btor->mm, bv1, bv2);
  for (res = 0; !btor_is_zero_bv (bv); res++)
  {
    bvdec = btor_add_bv (btor->mm, bv, ones);
    tmp   = bv;
    bv    = btor_and_bv (btor->mm, bv, bvdec);
    btor_free_bv (btor->mm, tmp);
    btor_free_bv (btor->mm, bvdec);
  }
  btor_free_bv (btor->mm, bv);
  btor_free_bv (btor->mm, ones);
  btor_free_bv (btor->mm, zero);
  return res;
}

// TODO find a better heuristic this might be too expensive
// this is not necessarily the actual minimum, but the minimum if you flip
// bits in bv1 s.t. bv1 < bv2 (if bv2 is 0, we need to flip 1 bit in bv2, too)
static int
min_flip (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int i, res;
  BtorBitVector *tmp;

  if (btor_is_zero_bv (bv2))
    res = hamming_distance (btor, bv1, bv2) + 1;
  else
  {
    tmp = btor_copy_bv (btor->mm, bv1);
    for (res = 1, i = tmp->width - 1; i >= 0; i--)
    {
      if (!btor_get_bit_bv (tmp, i)) continue;
      res += 1;
      btor_set_bit_bv (tmp, i, 0);
      if (btor_compare_bv (tmp, bv2) < 0) break;
    }
    if (btor_is_zero_bv (bv2)) res += 1;
    btor_free_bv (btor->mm, tmp);
  }
  return res;
}

static int
min_flip_inv (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int i, res;
  BtorBitVector *tmp;

  tmp = btor_copy_bv (btor->mm, bv1);
  for (res = 1, i = tmp->width - 1; i >= 0; i--)
  {
    if (btor_get_bit_bv (tmp, i)) continue;
    res += 1;
    btor_set_bit_bv (tmp, i, 1);
    if (btor_compare_bv (tmp, bv2) >= 0) break;
  }
  btor_free_bv (btor->mm, tmp);
  return res;
}

// score
//
// Boolean variable:
//   s (e[1], A) = A (e[1])
//
// bw m >= 1:
//
//   score (e0[bw] /\ e1[bw], A)    =
//       1/2 * (score (e0[bw], A) + score (e1[bw], A))
//
//   score (-(-e0[bw] /\ ... /\ -e1[bw]), A) =
//       max (score (-e0[bw], A), score (-e1[bw], A))
//
//   score (e0[bw] = e1[bw], A) =
//       (A (e0) == A (e1))
//	 ? 1.0
//	 : c1 * (1 - (h (A(e0), A(e1)) / bw)
//
//   score (e0[bw] != e1[bw], A) =
//       (A (e0) == A (e1) ? 0.0 : 1.0
//
//   s (e0[bw] < e1[bw], A) =
//       (A (e0) < A (e1))
//	 ? 1.0
//	 : c1 * (1 - (min number of bits to flip s.t. e0[bw] < e1[bw]) / bw)
//
static double
compute_sls_score_node (Btor *btor,
                        BtorPtrHashTable *bv_model,
                        BtorPtrHashTable *fun_model,
                        BtorPtrHashTable *score,
                        BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score);
  assert (exp);

  int i;
  double res, s0, s1;
  BtorNode *cur, *real_cur;
  BtorBitVector *bv0, *bv1;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorMemMgr *mm;
#ifndef NBTORLOG
  char *a0, *a1;
#endif

  res = 0.0;
  assert (btor_is_bv_eq_node (exp) || btor_is_ult_node (exp)
          || btor_get_exp_width (btor, exp) == 1);

  if ((b = btor_get_ptr_hash_table (score, exp))) return b->data.as_dbl;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  mark = btor_new_int_hash_map (mm);

  BTOR_PUSH_STACK (mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    d        = btor_get_int_hash_map (mark, real_cur->id);

    if ((d && d->as_int == 1) || btor_get_ptr_hash_table (score, cur)) continue;

    if (!d)
    {
      btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, stack, cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;

      if (!btor_is_bv_eq_node (real_cur) && !btor_is_ult_node (real_cur)
          && btor_get_exp_width (btor, real_cur) != 1)
        continue;

      BTORLOG (3, "");
      BTORLOG (3,
               "*** compute sls score for: %s(%s)",
               BTOR_IS_INVERTED_NODE (cur) ? "-" : " ",
               node2string (cur));

      if (btor_is_and_node (real_cur))
      {
        assert (btor_get_exp_width (btor, real_cur) == 1);
        if (BTOR_IS_INVERTED_NODE (cur))
        {
          assert (btor_get_ptr_hash_table (score,
                                           BTOR_INVERT_NODE (real_cur->e[0])));
          assert (btor_get_ptr_hash_table (score,
                                           BTOR_INVERT_NODE (real_cur->e[1])));

          s0 =
              btor_get_ptr_hash_table (score, BTOR_INVERT_NODE (real_cur->e[0]))
                  ->data.as_dbl;
          s1 =
              btor_get_ptr_hash_table (score, BTOR_INVERT_NODE (real_cur->e[1]))
                  ->data.as_dbl;
#ifndef NBTORLOG
          if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
          {
            a0 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, BTOR_INVERT_NODE (real_cur->e[0]));
            a1 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, BTOR_INVERT_NODE (real_cur->e[1]));
            BTORLOG (3, "      assignment e[0]: %s", a0);
            BTORLOG (3, "      assignment e[1]: %s", a1);
            btor_freestr (mm, a0);
            btor_freestr (mm, a1);
            BTORLOG (3, "      sls score e[0]: %f", s0);
            BTORLOG (3, "      sls score e[1]: %f", s1);
          }
#endif
          res = s0 > s1 ? s0 : s1;
        }
        else
        {
          assert (btor_get_ptr_hash_table (score, real_cur->e[0]));
          assert (btor_get_ptr_hash_table (score, real_cur->e[1]));

          s0 = btor_get_ptr_hash_table (score, real_cur->e[0])->data.as_dbl;
          s1 = btor_get_ptr_hash_table (score, (real_cur->e[1]))->data.as_dbl;
#ifndef NBTORLOG
          if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
          {
            a0 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, real_cur->e[0]);
            a1 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, real_cur->e[1]);
            BTORLOG (3, "      assignment e[0]: %s", a0);
            BTORLOG (3, "      assignment e[1]: %s", a1);
            btor_freestr (mm, a0);
            btor_freestr (mm, a1);
            BTORLOG (3, "      sls score e[0]: %f", s0);
            BTORLOG (3, "      sls score e[1]: %f", s1);
          }
#endif
          res = (s0 + s1) / 2.0;
          /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
             choose minimum (else it might again result in 1.0) */
          if (res == 1.0 && (s0 < 1.0 || s1 < 1.0)) res = s0 < s1 ? s0 : s1;
        }
      }
      else if (btor_is_bv_eq_node (real_cur))
      {
        bv0 = (BtorBitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[0]);
        bv1 = (BtorBitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[1]);
#ifndef NBTORLOG
        if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[1]);
          BTORLOG (3, "      assignment e[0]: %s", a0);
          BTORLOG (3, "      assignment e[1]: %s", a1);
          btor_freestr (mm, a0);
          btor_freestr (mm, a1);
        }
#endif
        if (BTOR_IS_INVERTED_NODE (cur))
          res = !btor_compare_bv (bv0, bv1) ? 0.0 : 1.0;
        else
          res = !btor_compare_bv (bv0, bv1)
                    ? 1.0
                    : BTOR_SLS_SCORE_CFACT
                          * (1.0
                             - hamming_distance (btor, bv0, bv1)
                                   / (double) bv0->width);
      }
      else if (btor_is_ult_node (real_cur))
      {
        bv0 = (BtorBitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[0]);
        bv1 = (BtorBitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[1]);
#ifndef NBTORLOG
        if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[1]);
          BTORLOG (3, "      assignment e[0]: %s", a0);
          BTORLOG (3, "      assignment e[1]: %s", a1);
          btor_freestr (mm, a0);
          btor_freestr (mm, a1);
        }
#endif
        if (BTOR_IS_INVERTED_NODE (cur))
          res = btor_compare_bv (bv0, bv1) >= 0
                    ? 1.0
                    : BTOR_SLS_SCORE_CFACT
                          * (1.0
                             - min_flip_inv (btor, bv0, bv1)
                                   / (double) bv0->width);
        else
          res = btor_compare_bv (bv0, bv1) < 0
                    ? 1.0
                    : BTOR_SLS_SCORE_CFACT
                          * (1.0
                             - min_flip (btor, bv0, bv1) / (double) bv0->width);
      }
      else
      {
        assert (btor_get_exp_width (btor, real_cur) == 1);
#ifndef NBTORLOG
        if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, cur);
          BTORLOG (3, "      assignment : %s", a0);
          btor_freestr (mm, a0);
        }
#endif
        res = ((BtorBitVector *) btor_get_bv_model_aux (
                   btor, bv_model, fun_model, cur))
                  ->bits[0];
      }

      assert (!btor_get_ptr_hash_table (score, cur));
      b              = btor_add_ptr_hash_table (score, cur);
      b->data.as_dbl = res;

      BTORLOG (3, "      sls score : %f", res);
    }
  }

  BTOR_RELEASE_STACK (mm, stack);
  btor_delete_int_hash_map (mark);

  assert (btor_get_ptr_hash_table (score, exp));
  assert (res == btor_get_ptr_hash_table (score, exp)->data.as_dbl);
  return res;
}

void
btor_propsls_compute_sls_scores (Btor *btor,
                                 BtorPtrHashTable *bv_model,
                                 BtorPtrHashTable *fun_model,
                                 BtorPtrHashTable *score)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score);

  int i;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack stack;
  BtorPtrHashTableIterator it;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorMemMgr *mm;

  BTORLOG (3, "");
  BTORLOG (3, "**** compute sls scores ***");

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  mark = btor_new_int_hash_map (mm);

  /* collect roots */
  btor_init_ptr_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    BTOR_PUSH_STACK (mm, stack, btor_next_ptr_hash_table_iterator (&it));

  /* compute score */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    d        = btor_get_int_hash_map (mark, real_cur->id);

    if ((d && d->as_int == 1) || btor_get_ptr_hash_table (score, cur)) continue;

    if (!d)
    {
      btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, stack, cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;
      if (!btor_is_bv_eq_node (real_cur) && !btor_is_ult_node (real_cur)
          && btor_get_exp_width (btor, real_cur) != 1)
        continue;
      compute_sls_score_node (btor, bv_model, fun_model, score, cur);
      compute_sls_score_node (
          btor, bv_model, fun_model, score, BTOR_INVERT_NODE (cur));
    }
  }

  BTOR_RELEASE_STACK (mm, stack);
  btor_delete_int_hash_map (mark);
}

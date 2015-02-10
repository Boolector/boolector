/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbitvec.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btordcr.h"
#include "btorhash.h"
#include "btoriter.h"
#include "btorlog.h"
#include "btormisc.h"
#include "btormodel.h"
#ifndef NBTORLOG
#include "btorprintmodel.h"
#endif

#include <math.h>

#define BTOR_SLS_MAXSTEPS_CFACT 100  // TODO best value? used by Z3
// TODO best restart scheme? used by Z3
#define BTOR_SLS_MAXSTEPS(i) \
  (BTOR_SLS_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BTOR_SLS_SCORE_CFACT 0.5  // TODO best value? used by Z3
#define BTOR_SLS_SELECT_CFACT 20  // TODO best value? used by Z3

static int
hamming_distance (Btor *btor, BitVector *bv1, BitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int res;
  BitVector *bv, *bvdec = 0, *zero, *ones, *tmp;

  zero = btor_new_bv (btor, bv1->width);
  ones = btor_not_bv (btor, zero);
  bv   = btor_xor_bv (btor, bv1, bv2);
  for (res = 0; !btor_compare_bv (bv, zero); res++)
  {
    bvdec = btor_add_bv (btor, bv, ones);
    tmp   = bv;
    bv    = btor_and_bv (btor, bv, bvdec);
    btor_free_bv (btor, tmp);
  }
  if (bvdec) btor_free_bv (btor, bvdec);
  btor_free_bv (btor, bv);
  btor_free_bv (btor, ones);
  btor_free_bv (btor, zero);
  return res;
}

// TODO find a better heuristic this might be to expensive
// this is not necessary the actual minimum, but the minimum if you flip
// bits in bv1 s.t. bv1 < bv2 (if bv2 is 0, we need to flip 1 bit in bv2, too)
static int
min_flip (Btor *btor, BitVector *bv1, BitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int i, res, b1;
  BitVector *tmp, *zero;

  zero = btor_new_bv (btor, bv2->width);
  tmp  = btor_copy_bv (btor, bv1);
  for (res = 0, i = tmp->width - 1; i >= 0; i--)
  {
    if (!(b1 = btor_get_bit_bv (tmp, i))) continue;
    res += 1;
    btor_set_bit_bv (tmp, i, 0);
    btor_print_bv (tmp);
    btor_print_bv (bv2);
    if (btor_compare_bv (tmp, bv2) < 0) break;
  }
  res = !btor_compare_bv (zero, bv2) ? res + 1 : res;
  btor_free_bv (btor, zero);
  btor_free_bv (btor, tmp);
  return res;
}

// score
//
// bw m == 1:
//   s (e[1], A) = A (e[1])
//
// bw m > 1:
//
//   score (e0[bw] /\ e1[bw], A)    =
//       1/2 * (score (e0[bw], A) + score (e1[bw], A))
//
//   score (-(e0[bw] /\ ... /\ e1[bw]), A) =
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
#if 1
static double
compute_sls_score_node (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor->score_sls);
  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (exp);

  int i;
  double res, s0, s1;
  BtorNode *real_exp, *cur, *real_cur, *e;
  BitVector *bv0, *bv1;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, unmark_stack;
#ifndef NBTORLOG
  char *a0, *a1;
#endif

  res      = 0.0;
  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (BTOR_IS_BV_EQ_NODE (real_exp) || BTOR_IS_ULT_NODE (real_exp)
          || real_exp->len == 1);

  if ((b = btor_find_in_ptr_hash_table (btor->score_sls, exp)))
    return b->data.asDbl;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  BTOR_PUSH_STACK (btor->mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->aux_mark == 2
        || btor_find_in_ptr_hash_table (btor->score_sls, cur))
      continue;

    if (real_cur->aux_mark == 0)
    {
      real_cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, stack, cur);
      BTOR_PUSH_STACK (btor->mm, unmark_stack, real_cur);

      if (BTOR_IS_AND_NODE (real_cur) && real_cur->len == 1)
      {
        for (i = 0; i < real_cur->arity; i++)
        {
          e = BTOR_IS_AND_NODE (real_cur) && BTOR_IS_INVERTED_NODE (cur)
                  ? BTOR_INVERT_NODE (real_cur->e[i])
                  : real_cur->e[i];
          BTOR_PUSH_STACK (btor->mm, stack, e);
        }
      }
    }
    else
    {
      assert (real_cur->aux_mark == 1);
      real_cur->aux_mark = 2;

      if (!BTOR_IS_BV_EQ_NODE (real_cur) && !BTOR_IS_ULT_NODE (real_cur)
          && real_cur->len != 1)
        continue;

      BTORLOG ("");
      BTORLOG ("*** compute sls score for: %s(%s)",
               BTOR_IS_INVERTED_NODE (cur) ? "-" : " ",
               node2string (cur));

      if (BTOR_IS_AND_NODE (real_cur))
      {
        assert (real_cur->len == 1);
        if (BTOR_IS_INVERTED_NODE (cur))
        {
          assert (btor_find_in_ptr_hash_table (
              btor->score_sls, BTOR_INVERT_NODE (real_cur->e[0])));
          assert (btor_find_in_ptr_hash_table (
              btor->score_sls, BTOR_INVERT_NODE (real_cur->e[1])));

          s0 = btor_find_in_ptr_hash_table (btor->score_sls,
                                            BTOR_INVERT_NODE (real_cur->e[0]))
                   ->data.asDbl;
          s1 = btor_find_in_ptr_hash_table (btor->score_sls,
                                            BTOR_INVERT_NODE (real_cur->e[1]))
                   ->data.asDbl;
#ifndef NBTORLOG
          if (btor->options.loglevel.val)
          {
            a0 = (char *) btor_get_bv_model_str (
                btor, BTOR_INVERT_NODE (real_cur->e[0]));
            a1 = (char *) btor_get_bv_model_str (
                btor, BTOR_INVERT_NODE (real_cur->e[1]));
            BTORLOG ("      assignment e[0]: %s", a0);
            BTORLOG ("      assignment e[1]: %s", a1);
            btor_freestr (btor->mm, a0);
            btor_freestr (btor->mm, a1);
            BTORLOG ("      sls score e[0]: %f", s0);
            BTORLOG ("      sls score e[1]: %f", s1);
          }
#endif
          res = s0 > s1 ? s0 : s1;
        }
        else
        {
          assert (
              btor_find_in_ptr_hash_table (btor->score_sls, real_cur->e[0]));
          assert (
              btor_find_in_ptr_hash_table (btor->score_sls, real_cur->e[1]));

          s0 = btor_find_in_ptr_hash_table (btor->score_sls, real_cur->e[0])
                   ->data.asDbl;
          s1 = btor_find_in_ptr_hash_table (btor->score_sls, (real_cur->e[1]))
                   ->data.asDbl;
#ifndef NBTORLOG
          if (btor->options.loglevel.val)
          {
            a0 = (char *) btor_get_bv_model_str (btor, real_cur->e[0]);
            a1 = (char *) btor_get_bv_model_str (btor, real_cur->e[1]);
            BTORLOG ("      assignment e[0]: %s", a0);
            BTORLOG ("      assignment e[1]: %s", a1);
            btor_freestr (btor->mm, a0);
            btor_freestr (btor->mm, a1);
            BTORLOG ("      sls score e[0]: %f", s0);
            BTORLOG ("      sls score e[1]: %f", s1);
          }
#endif
          res = (s0 + s1) / 2;
        }
      }
      else if (BTOR_IS_BV_EQ_NODE (real_cur))
      {
        bv0 = (BitVector *) btor_get_bv_model (btor, real_cur->e[0]);
        bv1 = (BitVector *) btor_get_bv_model (btor, real_cur->e[1]);
#ifndef NBTORLOG
        if (btor->options.loglevel.val)
        {
          a0 = (char *) btor_get_bv_model_str (btor, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str (btor, real_cur->e[1]);
          BTORLOG ("      assignment e[0]: %s", a0);
          BTORLOG ("      assignment e[1]: %s", a1);
          btor_freestr (btor->mm, a0);
          btor_freestr (btor->mm, a1);
        }
#endif
        if (BTOR_IS_INVERTED_NODE (cur))
          res = !btor_compare_bv (bv0, bv1) ? 0.0 : 1.0;
        else
          res = !btor_compare_bv (bv0, bv1)
                    ? 1.0
                    : BTOR_SLS_SCORE_CFACT
                          * (1 - hamming_distance (btor, bv0, bv1)) / 2;
      }
      else if (BTOR_IS_ULT_NODE (real_cur))
      {
        bv0 = (BitVector *) btor_get_bv_model (btor, real_cur->e[0]);
        bv1 = (BitVector *) btor_get_bv_model (btor, real_cur->e[1]);
#ifndef NBTORLOG
        if (btor->options.loglevel.val)
        {
          a0 = (char *) btor_get_bv_model_str (btor, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str (btor, real_cur->e[1]);
          BTORLOG ("      assignment e[0]: %s", a0);
          BTORLOG ("      assignment e[1]: %s", a1);
          btor_freestr (btor->mm, a0);
          btor_freestr (btor->mm, a1);
        }
#endif
        if (BTOR_IS_INVERTED_NODE (cur))
          res =
              btor_compare_bv (bv0, bv1) >= 0
                  ? 1.0
                  : BTOR_SLS_SCORE_CFACT * (1 - min_flip (btor, bv0, bv1) / 2);
        else
          res =
              btor_compare_bv (bv0, bv1) < 0
                  ? 1.0
                  : BTOR_SLS_SCORE_CFACT * (1 - min_flip (btor, bv0, bv1) / 2);
      }
      else
      {
        assert (real_cur->len == 1);
#ifndef NBTORLOG
        if (btor->options.loglevel.val)
        {
          a0 = (char *) btor_get_bv_model_str (btor, cur);
          BTORLOG ("      assignment : %s", a0);
          btor_freestr (btor->mm, a0);
        }
#endif
        res = ((BitVector *) btor_get_bv_model (btor, cur))->bits[0];
      }

      assert (!btor_find_in_ptr_hash_table (btor->score_sls, cur));
      b             = btor_insert_in_ptr_hash_table (btor->score_sls, cur);
      b->data.asDbl = res;

      BTORLOG ("      sls score : %f", res);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  BTOR_RELEASE_STACK (btor->mm, stack);

  assert (btor_find_in_ptr_hash_table (btor->score_sls, exp));
  assert (res
          == btor_find_in_ptr_hash_table (btor->score_sls, exp)->data.asDbl);
  return res;
}
#else
static double
compute_sls_score_node (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor->score_sls);
  assert (exp);

  double res, s0, s1;
  BtorNode *real_exp;
  BitVector *bv0, *bv1;
  BtorPtrHashBucket *b;
#ifndef NBTORLOG
  char *a0, *a1;
#endif

  BTORLOG ("");
  BTORLOG ("*** compute sls score for: %s(%s)",
           BTOR_IS_INVERTED_NODE (exp) ? "-" : " ",
           node2string (exp));

  res      = 0.0;
  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (BTOR_IS_BV_EQ_NODE (real_exp) || BTOR_IS_ULT_NODE (real_exp)
          || real_exp->len == 1);

  if ((b = btor_find_in_ptr_hash_table (btor->score_sls, exp)))
    return b->data.asDbl;

  if (BTOR_IS_AND_NODE (real_exp))
  {
    assert (real_exp->len == 1);
    if (BTOR_IS_INVERTED_NODE (exp))
    {
      assert (btor_find_in_ptr_hash_table (btor->score_sls,
                                           BTOR_INVERT_NODE (real_exp->e[0])));
      assert (btor_find_in_ptr_hash_table (btor->score_sls,
                                           BTOR_INVERT_NODE (real_exp->e[1])));

      s0 = btor_find_in_ptr_hash_table (btor->score_sls,
                                        BTOR_INVERT_NODE (real_exp->e[0]))
               ->data.asDbl;
      s1 = btor_find_in_ptr_hash_table (btor->score_sls,
                                        BTOR_INVERT_NODE (real_exp->e[1]))
               ->data.asDbl;
#ifndef NBTORLOG
      if (btor->options.loglevel.val)
      {
        a0 = (char *) btor_get_bv_model_str (btor,
                                             BTOR_INVERT_NODE (real_exp->e[0]));
        a1 = (char *) btor_get_bv_model_str (btor,
                                             BTOR_INVERT_NODE (real_exp->e[1]));
        BTORLOG ("      assignment e[0]: %s", a0);
        BTORLOG ("      assignment e[1]: %s", a1);
        btor_freestr (btor->mm, a0);
        btor_freestr (btor->mm, a1);
        BTORLOG ("      sls score e[0]: %f", s0);
        BTORLOG ("      sls score e[1]: %f", s1);
      }
#endif
      res = s0 > s1 ? s0 : s1;
    }
    else
    {
      assert (btor_find_in_ptr_hash_table (btor->score_sls, real_exp->e[0]));
      assert (btor_find_in_ptr_hash_table (btor->score_sls, real_exp->e[1]));

      s0 = btor_find_in_ptr_hash_table (btor->score_sls, real_exp->e[0])
               ->data.asDbl;
      s1 = btor_find_in_ptr_hash_table (btor->score_sls, (real_exp->e[1]))
               ->data.asDbl;
#ifndef NBTORLOG
      if (btor->options.loglevel.val)
      {
        a0 = (char *) btor_get_bv_model_str (btor, real_exp->e[0]);
        a1 = (char *) btor_get_bv_model_str (btor, real_exp->e[1]);
        BTORLOG ("      assignment e[0]: %s", a0);
        BTORLOG ("      assignment e[1]: %s", a1);
        btor_freestr (btor->mm, a0);
        btor_freestr (btor->mm, a1);
        BTORLOG ("      sls score e[0]: %f", s0);
        BTORLOG ("      sls score e[1]: %f", s1);
      }
#endif
      res = (s0 + s1) / 2;
    }
  }
  else if (BTOR_IS_BV_EQ_NODE (real_exp))
  {
    bv0 = (BitVector *) btor_get_bv_model (btor, real_exp->e[0]);
    bv1 = (BitVector *) btor_get_bv_model (btor, real_exp->e[1]);
#ifndef NBTORLOG
    if (btor->options.loglevel.val)
    {
      a0 = (char *) btor_get_bv_model_str (btor, real_exp->e[0]);
      a1 = (char *) btor_get_bv_model_str (btor, real_exp->e[1]);
      BTORLOG ("      assignment e[0]: %s", a0);
      BTORLOG ("      assignment e[1]: %s", a1);
      btor_freestr (btor->mm, a0);
      btor_freestr (btor->mm, a1);
    }
#endif
    if (BTOR_IS_INVERTED_NODE (exp))
      res = !btor_compare_bv (bv0, bv1) ? 0.0 : 1.0;
    else
      res = !btor_compare_bv (bv0, bv1)
                ? 1.0
                : BTOR_SLS_SCORE_CFACT * (1 - hamming_distance (btor, bv0, bv1))
                      / 2;
  }
  else if (BTOR_IS_ULT_NODE (real_exp))
  {
    bv0 = (BitVector *) btor_get_bv_model (btor, real_exp->e[0]);
    bv1 = (BitVector *) btor_get_bv_model (btor, real_exp->e[1]);
#ifndef NBTORLOG
    if (btor->options.loglevel.val)
    {
      a0 = (char *) btor_get_bv_model_str (btor, real_exp->e[0]);
      a1 = (char *) btor_get_bv_model_str (btor, real_exp->e[1]);
      BTORLOG ("      assignment e[0]: %s", a0);
      BTORLOG ("      assignment e[1]: %s", a1);
      btor_freestr (btor->mm, a0);
      btor_freestr (btor->mm, a1);
    }
#endif
    if (BTOR_IS_INVERTED_NODE (exp))
      res = btor_compare_bv (bv0, bv1) >= 0
                ? 1.0
                : BTOR_SLS_SCORE_CFACT * (1 - min_flip (btor, bv0, bv1)) / 2;
    else
      res = btor_compare_bv (bv0, bv1) < 1
                ? 1.0
                : BTOR_SLS_SCORE_CFACT * (1 - min_flip (btor, bv0, bv1)) / 2;
  }
  else
  {
    assert (real_exp->len == 1);
#ifndef NBTORLOG
    if (btor->options.loglevel.val)
    {
      a0 = (char *) btor_get_bv_model_str (btor, exp);
      BTORLOG ("      assignment : %s", a0);
      btor_freestr (btor->mm, a0);
    }
#endif
    res = ((BitVector *) btor_get_bv_model (btor, exp))->bits[0];
  }

  assert (!btor_find_in_ptr_hash_table (btor->score_sls, exp));
  b             = btor_insert_in_ptr_hash_table (btor->score_sls, exp);
  b->data.asDbl = res;
  BTORLOG ("      sls score : %f", res);

  return res;
}
#endif

static void
compute_sls_scores (Btor *btor, BtorPtrHashTable *roots)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (roots);

  int i;
  BtorNode *cur, *real_cur, *e;
  BtorNodePtrStack stack, unmark_stack;
  BtorHashTableIterator it;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  if (!btor->score_sls)
    btor->score_sls =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

  /* collect roots */
  init_node_hash_table_iterator (&it, roots);
  while (has_next_node_hash_table_iterator (&it))
    BTOR_PUSH_STACK (btor->mm, stack, next_node_hash_table_iterator (&it));

  /* compute score */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->mark == 2
        || btor_find_in_ptr_hash_table (btor->score_sls, cur))
      continue;

    if (real_cur->mark == 0)
    {
      real_cur->mark = 1;
      BTOR_PUSH_STACK (btor->mm, stack, cur);
      BTOR_PUSH_STACK (btor->mm, unmark_stack, real_cur);
      for (i = 0; i < real_cur->arity; i++)
      {
        e = BTOR_IS_INVERTED_NODE (cur) ? BTOR_INVERT_NODE (real_cur->e[i])
                                        : real_cur->e[i];
        BTOR_PUSH_STACK (btor->mm, stack, e);
      }
    }
    else
    {
      assert (real_cur->mark == 1);
      real_cur->mark = 2;
      if (!BTOR_IS_BV_EQ_NODE (real_cur) && !BTOR_IS_ULT_NODE (real_cur)
          && real_cur->len != 1)
        continue;
      compute_sls_score_node (btor, cur);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
}

static BtorNode *
select_candidate_constraint (Btor *btor, BtorPtrHashTable *roots, int moves)
{
  assert (btor);
  assert (btor->score_sls);
  assert (roots);

  int selected;
  double value, max_value, score;
  BtorNode *res, *cur;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b, *bucket;

  res       = 0;
  max_value = 0.0;
  bucket    = 0;
  init_hash_table_iterator (&it, roots);
  while (has_next_node_hash_table_iterator (&it))
  {
    b   = it.bucket;
    cur = next_node_hash_table_iterator (&it);
    assert (btor_find_in_ptr_hash_table (btor->score_sls, cur));
    score = btor_find_in_ptr_hash_table (btor->score_sls, cur)->data.asDbl;
    if (score >= 1.0) continue;
    if (!res)
    {
      res = cur;
      continue;
    }
    else
    {
      selected = b->data.asInt;
      value    = score + BTOR_SLS_SELECT_CFACT * sqrt (log (selected) / moves);
      if (value > max_value)
      {
        res       = cur;
        max_value = value;
        bucket    = b;
      }
    }
  }
  if (bucket) bucket->data.asInt += 1; /* n times selected */

  BTORLOG ("");
  BTORLOG ("*** select candidate constraint: %s\n", node2string (res));

  return res;
}

static void
select_candidates (Btor *btor, BtorNode *root, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (root);
  assert (candidates);

  int i;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack stack, unmark_stack;
  BitVector *bv, *bv0, *bv1;

  BTORLOG ("");
  BTORLOG ("*** select candidates");

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  assert (BTOR_COUNT_STACK (*candidates) == 0);
  BTOR_PUSH_STACK (btor->mm, stack, root);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    if (real_cur->mark) continue;
    real_cur->mark = 1;
    BTOR_PUSH_STACK (btor->mm, unmark_stack, real_cur);

    if (BTOR_IS_BV_VAR_NODE (real_cur))
    {
      BTOR_PUSH_STACK (btor->mm, *candidates, real_cur);
      BTORLOG ("  %s\n", node2string (real_cur));
      continue;
    }

    if (btor->options.sls_just.val)
    {
      /* choose candidates from controlling paths
       * (on the Boolean layer) only */
      if (BTOR_IS_AND_NODE (real_cur) && real_cur->len == 1)
      {
        bv  = (BitVector *) btor_get_bv_model (btor, real_cur);
        bv0 = (BitVector *) btor_get_bv_model (btor, real_cur->e[0]);
        bv1 = (BitVector *) btor_get_bv_model (btor, real_cur->e[1]);

        assert (bv->bits[0] == 1 || bv->bits[0] == 0);

        if (bv->bits[0] == 1)
          goto PUSH_CHILDREN;
        else
        {
          if (bv0->bits[0] == 0 && bv1->bits[0])
          {
            if (btor_compare_scores (btor, real_cur->e[0], real_cur->e[1]))
              BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[0]);
            else
              BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[1]);
          }
          else if (bv0->bits[0] == 0)
            BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[0]);
          else
          {
            assert (bv1->bits[0] == 0);
            BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[1]);
          }
        }
      }
      else
        goto PUSH_CHILDREN;
    }
    else
    {
    PUSH_CHILDREN:
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[i]);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
}

/* Note: failed assumptions -> no handling necessary, sls only works for SAT */
int
btor_sat_aux_btor_sls (Btor *btor)
{
  assert (btor);
  // TODO we currently support QF_BV only
  assert (btor->lambdas->count == 0 && btor->ufs->count == 0);

  int i, j;
  int sat_result, simp_sat_result;
  int moves;
  BtorPtrHashTable *roots;
  BtorHashTableIterator it;
  BtorNodePtrStack candidates;

  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  simp_sat_result = btor_simplify (btor);
  btor_update_assumptions (btor);

  if (btor->inconsistent) goto UNSAT;

  // do something

  BTOR_INIT_STACK (candidates);
  moves = 0;

  // TODO insert infinite loop here
  i = 1;
  /* Generate intial model, all bv vars are initialized with zero.
   * We do not have to consider model_for_all_nodes, but let this be handled
   * by the model generation (if enabled) after SAT has been determined. */
  btor_generate_model (btor, 0);

  /* collect roots */
  roots = btor_new_ptr_hash_table (btor->mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);
  assert (btor->synthesized_constraints->count == 0);
  init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  queue_node_hash_table_iterator (&it, btor->assumptions);
  while (has_next_node_hash_table_iterator (&it))
    btor_insert_in_ptr_hash_table (roots, next_node_hash_table_iterator (&it));

  // BitVector *bv1 = btor_uint64_to_bv (btor, 120, 7);
  // BitVector *bv2 = btor_uint64_to_bv (btor, 0, 7);
  // printf ("res: %d\n", min_flip (btor, bv1, bv2));
  compute_sls_scores (btor, roots);

  if (btor->options.sls_just.val)
  {
    btor->options.just_heuristic.val = BTOR_JUST_HEUR_BRANCH_MIN_DEP;
    btor_compute_scores (btor);
  }

  select_candidates (
      btor, select_candidate_constraint (btor, roots, moves), &candidates);

  // for (j = 0; j < BTOR_SLS_MAXSTEPS (i); j++)
  //  {
  //    // select candidate
  //    // find best move
  //    // if move update
  //    // else randomize
  //  }

UNSAT:
  sat_result = BTOR_UNSAT;
  goto DONE;

DONE:
  btor->last_sat_result = sat_result;
  /* cleanup */
  BTOR_RELEASE_STACK (btor->mm, candidates);
  btor_delete_ptr_hash_table (roots);
  return sat_result;
}

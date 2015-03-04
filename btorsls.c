/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorabort.h"
#include "btorbitvec.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btordcr.h"
#include "btorhash.h"
#include "btoriter.h"
#include "btorlog.h"
#include "btormisc.h"
#include "btormodel.h"
#ifndef NDEBUG
#include "btorclone.h"
#include "btorprintmodel.h"
#endif

#include <math.h>

#define BTOR_SLS_MAXSTEPS_CFACT 100  // TODO best value? used by Z3 (c4)
// TODO best restart scheme? used by Z3
#define BTOR_SLS_MAXSTEPS(i) \
  (BTOR_SLS_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BTOR_SLS_SCORE_CFACT 0.5      // TODO best value? used by Z3 (c1)
#define BTOR_SLS_SCORE_F_CFACT 0.025  // TODO best value? used by Z3 (c3)
#define BTOR_SLS_SCORE_F_PROB 20      // = 0.05 TODO best value? used by Z3 (sp)
#define BTOR_SLS_SELECT_CFACT 20      // TODO best value? used by Z3 (c2)

BTOR_DECLARE_STACK (BitVectorPtr, BitVector *);

static int
hamming_distance (Btor *btor, BitVector *bv1, BitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int res;
  BitVector *bv, *bvdec = 0, *zero, *ones, *tmp;

  zero = btor_new_bv (btor->mm, bv1->width);
  ones = btor_not_bv (btor->mm, zero);
  bv   = btor_xor_bv (btor->mm, bv1, bv2);
  for (res = 0; btor_compare_bv (bv, zero); res++)
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

  zero = btor_new_bv (btor->mm, bv2->width);
  tmp  = btor_copy_bv (btor->mm, bv1);
  for (res = 0, i = tmp->width - 1; i >= 0; i--)
  {
    if (!(b1 = btor_get_bit_bv (tmp, i))) continue;
    res += 1;
    btor_set_bit_bv (tmp, i, 0);
    if (btor_compare_bv (tmp, bv2) < 0) break;
  }
  res = !btor_compare_bv (zero, bv2) ? res + 1 : res;
  btor_free_bv (btor->mm, zero);
  btor_free_bv (btor->mm, tmp);
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
static double
compute_sls_score_node (Btor *btor,
                        BtorPtrHashTable **bv_model,
                        BtorPtrHashTable **fun_model,
                        BtorPtrHashTable *score_sls,
                        BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score_sls);
  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (exp);

  int i;
  double res, s0, s1;
  BtorNode *cur, *real_cur, *e;
  BitVector *bv0, *bv1;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, unmark_stack;
#ifndef NBTORLOG
  char *a0, *a1;
#endif

  res = 0.0;
  assert (BTOR_IS_BV_EQ_NODE (BTOR_REAL_ADDR_NODE (exp))
          || BTOR_IS_ULT_NODE (BTOR_REAL_ADDR_NODE (exp))
          || BTOR_REAL_ADDR_NODE (exp)->len == 1);

  if ((b = btor_find_in_ptr_hash_table (score_sls, exp))) return b->data.asDbl;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  BTOR_PUSH_STACK (btor->mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->aux_mark == 2 || btor_find_in_ptr_hash_table (score_sls, cur))
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
          e = BTOR_IS_INVERTED_NODE (cur) ? BTOR_INVERT_NODE (real_cur->e[i])
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

      //  BTORLOG ("");
      //  BTORLOG ("*** compute sls score for: %s(%s)",
      //	   BTOR_IS_INVERTED_NODE (cur) ? "-" : " ",
      //	   node2string (cur));

      if (BTOR_IS_AND_NODE (real_cur))
      {
        assert (real_cur->len == 1);
        if (BTOR_IS_INVERTED_NODE (cur))
        {
          assert (btor_find_in_ptr_hash_table (
              score_sls, BTOR_INVERT_NODE (real_cur->e[0])));
          assert (btor_find_in_ptr_hash_table (
              score_sls, BTOR_INVERT_NODE (real_cur->e[1])));

          s0 = btor_find_in_ptr_hash_table (score_sls,
                                            BTOR_INVERT_NODE (real_cur->e[0]))
                   ->data.asDbl;
          s1 = btor_find_in_ptr_hash_table (score_sls,
                                            BTOR_INVERT_NODE (real_cur->e[1]))
                   ->data.asDbl;
#ifndef NBTORLOG
          if (btor->options.loglevel.val)
          {
            a0 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, BTOR_INVERT_NODE (real_cur->e[0]));
            a1 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, BTOR_INVERT_NODE (real_cur->e[1]));
            // BTORLOG ("      assignment e[0]: %s", a0);
            // BTORLOG ("      assignment e[1]: %s", a1);
            btor_freestr (btor->mm, a0);
            btor_freestr (btor->mm, a1);
            // BTORLOG ("      sls score e[0]: %f", s0);
            // BTORLOG ("      sls score e[1]: %f", s1);
          }
#endif
          res = s0 > s1 ? s0 : s1;
        }
        else
        {
          assert (btor_find_in_ptr_hash_table (score_sls, real_cur->e[0]));
          assert (btor_find_in_ptr_hash_table (score_sls, real_cur->e[1]));

          s0 = btor_find_in_ptr_hash_table (score_sls, real_cur->e[0])
                   ->data.asDbl;
          s1 = btor_find_in_ptr_hash_table (score_sls, (real_cur->e[1]))
                   ->data.asDbl;
#ifndef NBTORLOG
          if (btor->options.loglevel.val)
          {
            a0 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, real_cur->e[0]);
            a1 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, real_cur->e[1]);
            // BTORLOG ("      assignment e[0]: %s", a0);
            // BTORLOG ("      assignment e[1]: %s", a1);
            btor_freestr (btor->mm, a0);
            btor_freestr (btor->mm, a1);
            // BTORLOG ("      sls score e[0]: %f", s0);
            // BTORLOG ("      sls score e[1]: %f", s1);
          }
#endif
          res = (s0 + s1) / 2.0;
        }
      }
      else if (BTOR_IS_BV_EQ_NODE (real_cur))
      {
        bv0 = (BitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[0]);
        bv1 = (BitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[1]);
#ifndef NBTORLOG
        if (btor->options.loglevel.val)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[1]);
          // BTORLOG ("      assignment e[0]: %s", a0);
          // BTORLOG ("      assignment e[1]: %s", a1);
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
                          * (1.0
                             - hamming_distance (btor, bv0, bv1)
                                   / (double) bv0->width);
      }
      else if (BTOR_IS_ULT_NODE (real_cur))
      {
        bv0 = (BitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[0]);
        bv1 = (BitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[1]);
#ifndef NBTORLOG
        if (btor->options.loglevel.val)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[1]);
          // BTORLOG ("      assignment e[0]: %s", a0);
          // BTORLOG ("      assignment e[1]: %s", a1);
          btor_freestr (btor->mm, a0);
          btor_freestr (btor->mm, a1);
        }
#endif
        if (BTOR_IS_INVERTED_NODE (cur))
          res = btor_compare_bv (bv0, bv1) >= 0
                    ? 1.0
                    : BTOR_SLS_SCORE_CFACT
                          * (1.0
                             - min_flip (btor, bv0, bv1) / (double) bv0->width);
        else
          res = btor_compare_bv (bv0, bv1) < 0
                    ? 1.0
                    : BTOR_SLS_SCORE_CFACT
                          * (1.0
                             - min_flip (btor, bv0, bv1) / (double) bv0->width);
      }
      else
      {
        assert (real_cur->len == 1);
        //#ifndef NBTORLOG
        //	      if (btor->options.loglevel.val)
        //		{
        //		  a0 = (char *) btor_get_bv_model_str_aux (
        //		      btor, bv_model, fun_model, cur);
        //		  BTORLOG ("      assignment : %s", a0);
        //		  btor_freestr (btor->mm, a0);
        //		}
        //#endif
        res = ((BitVector *) btor_get_bv_model_aux (
                   btor, bv_model, fun_model, cur))
                  ->bits[0];
      }

      assert (!btor_find_in_ptr_hash_table (score_sls, cur));
      b             = btor_insert_in_ptr_hash_table (score_sls, cur);
      b->data.asDbl = res;

      // BTORLOG ("      sls score : %f", res);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  BTOR_RELEASE_STACK (btor->mm, stack);

  assert (btor_find_in_ptr_hash_table (score_sls, exp));
  assert (res == btor_find_in_ptr_hash_table (score_sls, exp)->data.asDbl);
  return res;
}

static void
compute_sls_scores_aux (Btor *btor,
                        BtorPtrHashTable **bv_model,
                        BtorPtrHashTable **fun_model,
                        BtorPtrHashTable *roots,
                        BtorPtrHashTable *score)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (roots);

  // TODO early pruning!!!
  //
  int i;
  BtorNode *cur, *real_cur, *e;
  BtorNodePtrStack stack, unmark_stack;
  BtorHashTableIterator it;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  /* collect roots */
  init_node_hash_table_iterator (&it, roots);
  while (has_next_node_hash_table_iterator (&it))
    BTOR_PUSH_STACK (btor->mm, stack, next_node_hash_table_iterator (&it));

  /* compute score */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->mark == 2 || btor_find_in_ptr_hash_table (score, cur))
      continue;

    if (real_cur->mark == 0)
    {
      real_cur->mark = 1;
      BTOR_PUSH_STACK (btor->mm, stack, cur);
      BTOR_PUSH_STACK (btor->mm, unmark_stack, real_cur);
      for (i = 0; i < real_cur->arity; i++)
      {
        e = BTOR_IS_AND_NODE (real_cur) && real_cur->len == 1
                    && BTOR_IS_INVERTED_NODE (cur)
                ? BTOR_INVERT_NODE (real_cur->e[i])
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
      compute_sls_score_node (btor, bv_model, fun_model, score, cur);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
}

static void
compute_sls_scores (Btor *btor,
                    BtorPtrHashTable *roots,
                    BtorPtrHashTable *score)
{
  assert (btor);
  assert (roots);
  assert (score);

  compute_sls_scores_aux (
      btor, &btor->bv_model, &btor->fun_model, roots, score);
}

static double
compute_sls_score_formula (BtorPtrHashTable *roots, BtorPtrHashTable *score)
{
  assert (roots);
  assert (score);

  int allsat;
  double res, sc, weight;
  BtorNode *root;
  BtorHashTableIterator it;

  res    = 0.0;
  allsat = 1;
  init_node_hash_table_iterator (&it, roots);
  while (has_next_node_hash_table_iterator (&it))
  {
    weight = (double) it.bucket->data.asInt;
    root   = next_node_hash_table_iterator (&it);
    sc     = btor_find_in_ptr_hash_table (score, root)->data.asDbl;
    if (sc < 1.0) allsat = 0;
    res += weight * sc;
  }
  return allsat ? -1.0 : res;
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

  assert (res);

  BTORLOG ("");
  BTORLOG ("*** select candidate constraint: %s", node2string (res));

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
  double sc;
  BtorNode *cur, *real_cur, *e;
  BtorNodePtrStack stack, unmark_stack;

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
      BTORLOG ("  %s", node2string (real_cur));
      continue;
    }

    /* push children */
    if (BTOR_IS_AND_NODE (real_cur) && real_cur->len == 1)
    {
      for (i = 0; i < real_cur->arity; i++)
      {
        e = BTOR_IS_INVERTED_NODE (cur) ? BTOR_INVERT_NODE (real_cur->e[i])
                                        : real_cur->e[i];
        assert (btor_find_in_ptr_hash_table (btor->score_sls, e));
        sc = btor_find_in_ptr_hash_table (btor->score_sls, e)->data.asDbl;
        if (sc == 1.0) continue;
        BTOR_PUSH_STACK (btor->mm, stack, e);
      }
    }
    else
    {
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

static void *
copy_node (BtorMemMgr *mm, const void *map, const void *key)
{
  assert (mm);
  assert (key);

  BtorNode *cloned_exp;

  (void) mm;
  (void) map;
  cloned_exp = (BtorNode *) key;
  cloned_exp =
      btor_copy_exp (BTOR_REAL_ADDR_NODE (cloned_exp)->btor, cloned_exp);
  return cloned_exp;
}

static void *
same_node (BtorMemMgr *mm, const void *map, const void *key)
{
  assert (mm);
  assert (key);

  (void) mm;
  (void) map;
  return (BtorNode *) key;
}

static void
data_as_bv_ptr (BtorMemMgr *mm,
                const void *map,
                BtorPtrHashData *data,
                BtorPtrHashData *cloned_data)
{
  assert (mm);
  assert (data);
  assert (cloned_data);

  (void) map;
  cloned_data->asPtr = btor_copy_bv (mm, (BitVector *) data->asPtr);
}

static void
data_as_double (BtorMemMgr *mm,
                const void *map,
                BtorPtrHashData *data,
                BtorPtrHashData *cloned_data)
{
  assert (mm);
  assert (data);
  assert (cloned_data);

  (void) mm;
  (void) map;
  cloned_data->asDbl = data->asDbl;
}

static void
reset_cone (Btor *btor,
            BtorNodePtrStack *exps,
            BtorPtrHashTable *bv_model,
            BtorPtrHashTable *score_sls)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (exps);
  assert (BTOR_COUNT_STACK (*exps));
  assert (bv_model);
  assert (score_sls);

  int i;
  BtorNode *cur;
  BtorNodeIterator nit;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, unmark_stack;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  for (i = 0; i < BTOR_COUNT_STACK (*exps); i++)
    BTOR_PUSH_STACK (btor->mm, stack, BTOR_PEEK_STACK (*exps, i));

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->mark) continue;
    cur->mark = 1;
    BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

    /* reset previous assignment */
    if ((b = btor_find_in_ptr_hash_table (bv_model, cur)))
    {
      btor_free_bv (btor->mm, b->data.asPtr);
      btor_remove_from_ptr_hash_table (bv_model, cur, 0, 0);
      btor_release_exp (btor, cur);
    }
    if ((b = btor_find_in_ptr_hash_table (bv_model, BTOR_INVERT_NODE (cur))))
    {
      btor_free_bv (btor->mm, b->data.asPtr);
      btor_remove_from_ptr_hash_table (bv_model, BTOR_INVERT_NODE (cur), 0, 0);
      btor_release_exp (btor, cur);
    }
    /* reset previous score */
    if ((b = btor_find_in_ptr_hash_table (score_sls, cur)))
      btor_remove_from_ptr_hash_table (score_sls, cur, 0, 0);
    if ((b = btor_find_in_ptr_hash_table (score_sls, BTOR_INVERT_NODE (cur))))
      btor_remove_from_ptr_hash_table (score_sls, BTOR_INVERT_NODE (cur), 0, 0);

    /* push parents */
    init_full_parent_iterator (&nit, cur);
    while (has_next_parent_full_parent_iterator (&nit))
      BTOR_PUSH_STACK (
          btor->mm, stack, next_parent_full_parent_iterator (&nit));
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
}

static void
update_cone (Btor *btor,
             BtorPtrHashTable **bv_model,
             BtorPtrHashTable **fun_model,
             BtorPtrHashTable *roots,
             BtorNodePtrStack *exps,
             BitVectorPtrStack *assignments,
             BtorPtrHashTable *score_sls)
{
  assert (btor);
  assert (bv_model);
  assert (*bv_model);
  assert (fun_model);
  assert (*fun_model);
  assert (roots);
  assert (exps);
  assert (BTOR_COUNT_STACK (*exps));
  assert (assignments);
  assert (BTOR_COUNT_STACK (*exps) == BTOR_COUNT_STACK (*assignments));
  assert (score_sls);

  int i;
  BtorNode *exp;
  BitVector *assignment;

  reset_cone (btor, exps, *bv_model, score_sls);

  for (i = 0; i < BTOR_COUNT_STACK (*exps); i++)
  {
    exp        = BTOR_PEEK_STACK (*exps, i);
    assignment = BTOR_PEEK_STACK (*assignments, i);
    btor_add_to_bv_model (btor, *bv_model, exp, assignment);
  }

  btor_generate_model_aux (btor, *bv_model, *fun_model, 0);
  compute_sls_scores_aux (btor, bv_model, fun_model, roots, score_sls);
}

static void
move (Btor *btor, BtorPtrHashTable *roots, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (roots);
  assert (candidates);

  int i, j, r, randomized, randomizeall;
  double max_score, sc;
  BtorNode *can, *max_can, *cur;
  BitVector *ass, *neighbor, *max_neighbor;
  BtorPtrHashTable *bv_model, *score_sls;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorNodePtrStack cans;
  BitVectorPtrStack neighbors;
#ifndef NBTORLOG
  char *a;
#endif

  btor->stats.sls_moves += 1;

  BTOR_INIT_STACK (cans);
  BTOR_INIT_STACK (neighbors);

  /** select move **/
  max_score    = compute_sls_score_formula (roots, btor->score_sls);
  max_neighbor = 0;
  max_can      = 0;
  randomized   = 0;

  for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
  {
    can = BTOR_PEEK_STACK (*candidates, i);
    assert (BTOR_IS_REGULAR_NODE (can));
    ass = (BitVector *) btor_get_bv_model (btor, can);
    assert (ass);

    bv_model = btor_clone_ptr_hash_table (
        btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
    score_sls = btor_clone_ptr_hash_table (
        btor->mm, btor->score_sls, same_node, data_as_double, 0, 0);

    /* flip bits */
    for (j = 0; j < ass->width; j++)
    {
      btor->stats.sls_flips += 1;
      neighbor = btor->options.sls_move_inc_move_test.val && max_neighbor
                         && max_neighbor->width == ass->width
                     ? btor_copy_bv (btor->mm, max_neighbor)
                     : btor_copy_bv (btor->mm, ass);
      btor_flip_bit_bv (neighbor, j);
#ifndef NBTORLOG
      BTORLOG ("");
      BTORLOG (" try: flip %d", j);
      BTORLOG ("  candidate: %s%s",
               BTOR_IS_REGULAR_NODE (max_can) ? "" : "-",
               node2string (can));
      a = btor_bv_to_char_bv (btor->mm, ass);
      BTORLOG ("  prev. assignment: %s", a);
      btor_freestr (btor->mm, a);
      a = btor_bv_to_char_bv (btor->mm, neighbor);
      BTORLOG ("  new   assignment: %s", a);
      btor_freestr (btor->mm, a);
#endif
      BTOR_PUSH_STACK (btor->mm, cans, can);
      BTOR_PUSH_STACK (btor->mm, neighbors, neighbor);
      /* we currently support QF_BV only, hence no funs */
      update_cone (btor,
                   &bv_model,
                   &btor->fun_model,
                   roots,
                   &cans,
                   &neighbors,
                   score_sls);

      if ((sc = compute_sls_score_formula (roots, score_sls)) == -1.0)
      {
        if (max_neighbor) btor_free_bv (btor->mm, max_neighbor);
        btor_delete_bv_model (btor, &bv_model);
        btor_delete_ptr_hash_table (score_sls);
        goto MOVE;
      }

      BTOR_RESET_STACK (cans);
      BTOR_RESET_STACK (neighbors);

      if (sc > max_score)
      {
        max_score = sc;
        if (max_neighbor) btor_free_bv (btor->mm, max_neighbor);
        max_neighbor = neighbor;
        max_can      = can;
        if (btor->options.sls_move_on_first.val)
        {
          btor_delete_bv_model (btor, &bv_model);
          btor_delete_ptr_hash_table (score_sls);
          goto MOVE;
        }
      }
      else
        btor_free_bv (btor->mm, neighbor);
    }

    /* increment */
    btor->stats.sls_flips += 1;
    neighbor = btor->options.sls_move_inc_move_test.val && max_neighbor
                       && max_neighbor->width == ass->width
                   ? btor_copy_bv (btor->mm, max_neighbor)
                   : btor_copy_bv (btor->mm, ass);
#ifndef NBTORLOG
    BTORLOG ("");
    BTORLOG (" try: increment");
    BTORLOG ("  candidate: %s%s",
             BTOR_IS_REGULAR_NODE (max_can) ? "" : "-",
             node2string (can));
    a = btor_bv_to_char_bv (btor->mm, ass);
    BTORLOG ("  prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char_bv (btor->mm, neighbor);
    BTORLOG ("  new   assignment: %s", a);
    btor_freestr (btor->mm, a);
#endif
    BTOR_PUSH_STACK (btor->mm, cans, can);
    BTOR_PUSH_STACK (btor->mm, neighbors, neighbor);
    update_cone (
        btor, &bv_model, &btor->fun_model, roots, &cans, &neighbors, score_sls);

    if ((sc = compute_sls_score_formula (roots, score_sls)) == -1.0)
    {
      if (max_neighbor) btor_free_bv (btor->mm, max_neighbor);
      btor_delete_bv_model (btor, &bv_model);
      btor_delete_ptr_hash_table (score_sls);
      goto MOVE;
    }

    BTOR_RESET_STACK (cans);
    BTOR_RESET_STACK (neighbors);

    if (sc > max_score)
    {
      max_score = sc;
      if (max_neighbor) btor_free_bv (btor->mm, max_neighbor);
      max_neighbor = neighbor;
      max_can      = can;
      if (btor->options.sls_move_on_first.val)
      {
        btor_delete_bv_model (btor, &bv_model);
        btor_delete_ptr_hash_table (score_sls);
        goto MOVE;
      }
    }
    else
      btor_free_bv (btor->mm, neighbor);

    /* decrement */
    btor->stats.sls_flips += 1;
    neighbor = btor->options.sls_move_inc_move_test.val && max_neighbor
                       && max_neighbor->width == ass->width
                   ? btor_copy_bv (btor->mm, max_neighbor)
                   : btor_copy_bv (btor->mm, ass);
#ifndef NBTORLOG
    BTORLOG ("");
    BTORLOG (" try: decrement");
    BTORLOG ("  candidate: %s%s",
             BTOR_IS_REGULAR_NODE (max_can) ? "" : "-",
             node2string (can));
    a = btor_bv_to_char_bv (btor->mm, ass);
    BTORLOG ("  prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char_bv (btor->mm, neighbor);
    BTORLOG ("  new   assignment: %s", a);
    btor_freestr (btor->mm, a);
#endif
    BTOR_PUSH_STACK (btor->mm, cans, can);
    BTOR_PUSH_STACK (btor->mm, neighbors, neighbor);
    update_cone (
        btor, &bv_model, &btor->fun_model, roots, &cans, &neighbors, score_sls);

    if ((sc = compute_sls_score_formula (roots, score_sls)) == -1.0)
    {
      if (max_neighbor) btor_free_bv (btor->mm, max_neighbor);
      btor_delete_bv_model (btor, &bv_model);
      btor_delete_ptr_hash_table (score_sls);
      goto MOVE;
    }

    BTOR_RESET_STACK (cans);
    BTOR_RESET_STACK (neighbors);

    if (sc > max_score)
    {
      max_score = sc;
      if (max_neighbor) btor_free_bv (btor->mm, max_neighbor);
      max_neighbor = neighbor;
      max_can      = can;
      if (btor->options.sls_move_on_first.val)
      {
        btor_delete_bv_model (btor, &bv_model);
        btor_delete_ptr_hash_table (score_sls);
        goto MOVE;
      }
    }
    else
      btor_free_bv (btor->mm, neighbor);

    /* not */
    btor->stats.sls_flips += 1;
    neighbor = btor->options.sls_move_inc_move_test.val && max_neighbor
                       && max_neighbor->width == ass->width
                   ? btor_copy_bv (btor->mm, max_neighbor)
                   : btor_copy_bv (btor->mm, ass);
#ifndef NBTORLOG
    BTORLOG ("");
    BTORLOG (" try: not");
    BTORLOG ("  candidate: %s%s",
             BTOR_IS_REGULAR_NODE (max_can) ? "" : "-",
             node2string (can));
    a = btor_bv_to_char_bv (btor->mm, ass);
    BTORLOG ("  prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char_bv (btor->mm, neighbor);
    BTORLOG ("  new   assignment: %s", a);
    btor_freestr (btor->mm, a);
#endif
    BTOR_PUSH_STACK (btor->mm, cans, can);
    BTOR_PUSH_STACK (btor->mm, neighbors, neighbor);
    update_cone (
        btor, &bv_model, &btor->fun_model, roots, &cans, &neighbors, score_sls);

    if ((sc = compute_sls_score_formula (roots, score_sls)) == -1.0)
    {
      if (max_neighbor) btor_free_bv (btor->mm, max_neighbor);
      btor_delete_bv_model (btor, &bv_model);
      btor_delete_ptr_hash_table (score_sls);
      goto MOVE;
    }

    BTOR_RESET_STACK (cans);
    BTOR_RESET_STACK (neighbors);

    if (sc > max_score)
    {
      max_score = sc;
      if (max_neighbor) btor_free_bv (btor->mm, max_neighbor);
      max_neighbor = neighbor;
      max_can      = can;
      if (btor->options.sls_move_on_first.val)
      {
        btor_delete_bv_model (btor, &bv_model);
        btor_delete_ptr_hash_table (score_sls);
        goto MOVE;
      }
    }
    else
      btor_free_bv (btor->mm, neighbor);

    /* cleanup */
    btor_delete_bv_model (btor, &bv_model);
    btor_delete_ptr_hash_table (score_sls);
  }

  if (max_neighbor)
  {
    assert (max_can);
    assert (BTOR_COUNT_STACK (cans) == 0);
    assert (BTOR_COUNT_STACK (neighbors) == 0);
    BTOR_PUSH_STACK (btor->mm, cans, max_can);
    BTOR_PUSH_STACK (btor->mm, neighbors, max_neighbor);
  }
  else
  {
    /* randomize if no best move was found */
    randomized   = 1;
    randomizeall = btor->options.sls_move_randomizeall.val
                       ? btor_pick_rand_rng (&btor->rng, 0, 1)
                       : 0;

    if (randomizeall)
    {
      for (r = 0; r < BTOR_COUNT_STACK (*candidates) - 1; r++)
      {
        can = BTOR_PEEK_STACK (*candidates, r);
        BTOR_PUSH_STACK (btor->mm, cans, can);
        if (BTOR_REAL_ADDR_NODE (can)->len == 1)
        {
          ass      = (BitVector *) btor_get_bv_model (btor, can);
          neighbor = btor_copy_bv (btor->mm, ass);
          btor_flip_bit_bv (neighbor, 0);
          BTOR_PUSH_STACK (btor->mm, neighbors, neighbor);
        }
        else
        {
          BTOR_PUSH_STACK (btor->mm,
                           neighbors,
                           btor_new_random_bv (btor->mm, &btor->rng, can->len));
        }
      }
    }
    else
    {
      r = btor_pick_rand_rng (
          &btor->rng, 0, BTOR_COUNT_STACK (*candidates) - 1);
      can = BTOR_PEEK_STACK (*candidates, r);
      BTOR_PUSH_STACK (btor->mm, cans, can);
      if (BTOR_REAL_ADDR_NODE (can)->len == 1)
      {
        ass      = (BitVector *) btor_get_bv_model (btor, can);
        neighbor = btor_copy_bv (btor->mm, ass);
        btor_flip_bit_bv (neighbor, 0);
        BTOR_PUSH_STACK (btor->mm, neighbors, neighbor);
      }
      else
        BTOR_PUSH_STACK (btor->mm,
                         neighbors,
                         btor_new_random_bv (btor->mm, &btor->rng, can->len));
    }
  }

MOVE:
  /** move **/
#ifndef NBTORLOG
  BTORLOG ("");
  BTORLOG ("*** move");
  assert (BTOR_COUNT_STACK (cans) == BTOR_COUNT_STACK (neighbors));
  for (i = 0; i < BTOR_COUNT_STACK (cans); i++)
  {
    can      = BTOR_PEEK_STACK (cans, i);
    neighbor = BTOR_PEEK_STACK (neighbors, i);
    ass      = (BitVector *) btor_get_bv_model (btor, can);
    a        = btor_bv_to_char_bv (btor->mm, ass);
    BTORLOG ("  candidate: %s%s",
             BTOR_IS_REGULAR_NODE (can) ? "" : "-",
             node2string (can));
    BTORLOG ("  prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char_bv (btor->mm, neighbor);
    BTORLOG ("  new   assignment: %s", a);
    btor_freestr (btor->mm, a);
  }
#endif

  update_cone (btor,
               &btor->bv_model,
               &btor->fun_model,
               roots,
               &cans,
               &neighbors,
               btor->score_sls);

  /** update assertion weights **/
  if (randomized)
  {
    if (!btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_SCORE_F_PROB))
    {
      /* decrease the weight of all satisfied assertions */
      init_node_hash_table_iterator (&it, roots);
      while (has_next_node_hash_table_iterator (&it))
      {
        b   = it.bucket;
        cur = next_node_hash_table_iterator (&it);
        if (btor_find_in_ptr_hash_table (btor->score_sls, cur)->data.asDbl
            == 0.0)
          continue;
        if (b->data.asInt > 1) b->data.asInt -= 1;
      }
    }
    else
    {
      /* increase the weight of all unsatisfied assertions */
      init_node_hash_table_iterator (&it, roots);
      while (has_next_node_hash_table_iterator (&it))
      {
        b   = it.bucket;
        cur = next_node_hash_table_iterator (&it);
        if (btor_find_in_ptr_hash_table (btor->score_sls, cur)->data.asDbl
            == 1.0)
          continue;
        b->data.asInt += 1;
      }
    }
  }

  /** cleanup **/
  BTOR_RELEASE_STACK (btor->mm, cans);
  while (!BTOR_EMPTY_STACK (neighbors))
    btor_free_bv (btor->mm, BTOR_POP_STACK (neighbors));
  BTOR_RELEASE_STACK (btor->mm, neighbors);
}

/* Note: failed assumptions -> no handling necessary, sls only works for SAT */
int
btor_sat_aux_btor_sls (Btor *btor)
{
  assert (btor);

  int i, j, max_steps;
  int sat_result;
  int moves;
  BtorPtrHashTable *roots;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorNodePtrStack candidates;

  roots = 0;
  moves = 0;

  //#ifndef NDEBUG
  //  Btor *clone = btor_clone_exp_layer (btor, 0, 0);
  //  clone->options.sls.val = 0;
  //  clone->options.auto_cleanup.val = 1;
  //  clone->options.auto_cleanup_internal.val = 1;
  //  clone->options.loglevel.val = 0;
  //  clone->options.verbosity.val = 0;
  //  clone->options.model_gen.val = 1;
  //  int csat_result = btor_sat_btor (clone, -1, -1);
  //  btor_delete_btor (clone);
  //  if (csat_result == BTOR_UNSAT) goto UNSAT;
  //  if (btor->lambdas->count || btor->ufs->count)
  //    {
  //      sat_result = csat_result;
  //      goto DONE;
  //    }
  //#endif
  BTOR_ABORT_BOOLECTOR (btor->lambdas->count != 0 || btor->ufs->count != 0,
                        "sls engine supports QF_BV only");

  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  sat_result = btor_simplify (btor);
  btor_update_assumptions (btor);

  if (btor->inconsistent) goto UNSAT;

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  btor_generate_model (btor, 0);

  /* collect roots */
  roots = btor_new_ptr_hash_table (btor->mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);
  assert (btor->synthesized_constraints->count == 0);
  init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  queue_node_hash_table_iterator (&it, btor->assumptions);
  while (has_next_node_hash_table_iterator (&it))
  {
    b             = btor_insert_in_ptr_hash_table (roots,
                                       next_node_hash_table_iterator (&it));
    b->data.asInt = 1; /* initial assertion weight */
  }

  BTOR_INIT_STACK (candidates);

  if (!btor->score_sls)
    btor->score_sls =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

  i = 1;
  for (;;)
  {
    /* compute initial sls score */
    compute_sls_scores (btor, roots, btor->score_sls);

    if (compute_sls_score_formula (roots, btor->score_sls) == -1.0)
    {
      sat_result = BTOR_SAT;
      goto SAT;
    }

    for (j = 0, max_steps = BTOR_SLS_MAXSTEPS (i); j < max_steps; j++)
    {
      select_candidates (
          btor, select_candidate_constraint (btor, roots, moves), &candidates);

      move (btor, roots, &candidates);

      if (compute_sls_score_formula (roots, btor->score_sls) == -1.0)
      {
        sat_result = BTOR_SAT;
        goto SAT;
      }

      BTOR_RESET_STACK (candidates);
    }

    /* restart */
    btor_generate_model (btor, 0);
    i += 1;
  }

SAT:
  assert (sat_result == BTOR_SAT);
  btor->stats.sls_restarts = i - 1;
  BTOR_RELEASE_STACK (btor->mm, candidates);
  goto DONE;

UNSAT:
  sat_result = BTOR_UNSAT;

DONE:
  if (roots) btor_delete_ptr_hash_table (roots);
  btor->last_sat_result = sat_result;
  return sat_result;
}

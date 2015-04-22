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
#include "btorclone.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorlog.h"
#include "btormodel.h"
#include "utils/btorhash.h"
#include "utils/btoriter.h"
#include "utils/btormap.h"
#include "utils/btormisc.h"
#ifndef NDEBUG
#include "btorprintmodel.h"
#endif

#include <math.h>

#define BTOR_SLS_MAXSTEPS_CFACT 100  // TODO best value? used by Z3 (c4)
// TODO best restart scheme? used by Z3
#define BTOR_SLS_MAXSTEPS(i) \
  (BTOR_SLS_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BTOR_SLS_SCORE_CFACT 0.5      // TODO best value? used by Z3 (c1)
#define BTOR_SLS_SCORE_F_CFACT 0.025  // TODO best value? used by Z3 (c3)
#define BTOR_SLS_SELECT_CFACT 20      // TODO best value? used by Z3 (c2)

#define BTOR_SLS_PROB_SCORE_F 20  // = 0.05 TODO best value? used by Z3 (sp)

/* choose move with one candidate rather than group wise move for random walk */
#define BTOR_SLS_PROB_SINGLE_VS_GW 20
/* randomize all candidates rather than one only */
#define BTOR_SLS_PROB_RAND_ALL_VS_ONE 1
/* start ranges from LSB rather than MSB */
#define BTOR_SLS_PROB_RANGE_LSB_VS_MSB 1
/* start segments from LSB rather than MSB */
#define BTOR_SLS_PROB_SEG_LSB_VS_MSB 1

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
  for (res = 0; btor_is_zero_bv (bv); res++)
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
  BitVector *tmp;

  tmp = btor_copy_bv (btor->mm, bv1);
  for (res = 0, i = tmp->width - 1; i >= 0; i--)
  {
    if (!(b1 = btor_get_bit_bv (tmp, i))) continue;
    res += 1;
    btor_set_bit_bv (tmp, i, 0);
    if (btor_compare_bv (tmp, bv2) < 0) break;
  }
  res = btor_is_zero_bv (bv2) ? res + 1 : res;
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

//#ifndef NBTORLOG
//#define BTOR_SLS_LOG_COMPUTE_SCORE
//#endif

static double
compute_sls_score_node (Btor *btor,
                        BtorPtrHashTable **bv_model,
                        BtorPtrHashTable **fun_model,
                        BtorPtrHashTable *score,
                        BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score);
  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (exp);

  int i;
  double res, s0, s1;
  BtorNode *cur, *real_cur;
  BitVector *bv0, *bv1;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, unmark_stack;
#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
  char *a0, *a1;
#endif

  res = 0.0;
  assert (BTOR_IS_BV_EQ_NODE (BTOR_REAL_ADDR_NODE (exp))
          || BTOR_IS_ULT_NODE (BTOR_REAL_ADDR_NODE (exp))
          || BTOR_REAL_ADDR_NODE (exp)->len == 1);

  if ((b = btor_find_in_ptr_hash_table (score, exp))) return b->data.asDbl;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  BTOR_PUSH_STACK (btor->mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->aux_mark == 2 || btor_find_in_ptr_hash_table (score, cur))
      continue;

    if (real_cur->aux_mark == 0)
    {
      real_cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, stack, cur);
      BTOR_PUSH_STACK (btor->mm, unmark_stack, real_cur);

      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[i]);
    }
    else
    {
      assert (real_cur->aux_mark == 1);
      real_cur->aux_mark = 2;

      if (!BTOR_IS_BV_EQ_NODE (real_cur) && !BTOR_IS_ULT_NODE (real_cur)
          && real_cur->len != 1)
        continue;

#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
      BTORLOG ("");
      BTORLOG ("*** compute sls score for: %s(%s)",
               BTOR_IS_INVERTED_NODE (cur) ? "-" : " ",
               node2string (cur));
#endif

      if (BTOR_IS_AND_NODE (real_cur))
      {
        assert (real_cur->len == 1);
        if (BTOR_IS_INVERTED_NODE (cur))
        {
          assert (btor_find_in_ptr_hash_table (
              score, BTOR_INVERT_NODE (real_cur->e[0])));
          assert (btor_find_in_ptr_hash_table (
              score, BTOR_INVERT_NODE (real_cur->e[1])));

          s0 = btor_find_in_ptr_hash_table (score,
                                            BTOR_INVERT_NODE (real_cur->e[0]))
                   ->data.asDbl;
          s1 = btor_find_in_ptr_hash_table (score,
                                            BTOR_INVERT_NODE (real_cur->e[1]))
                   ->data.asDbl;
#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
          if (btor->options.loglevel.val)
          {
            a0 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, BTOR_INVERT_NODE (real_cur->e[0]));
            a1 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, BTOR_INVERT_NODE (real_cur->e[1]));
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
          assert (btor_find_in_ptr_hash_table (score, real_cur->e[0]));
          assert (btor_find_in_ptr_hash_table (score, real_cur->e[1]));

          s0 = btor_find_in_ptr_hash_table (score, real_cur->e[0])->data.asDbl;
          s1 =
              btor_find_in_ptr_hash_table (score, (real_cur->e[1]))->data.asDbl;
#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
          if (btor->options.loglevel.val)
          {
            a0 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, real_cur->e[0]);
            a1 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, real_cur->e[1]);
            BTORLOG ("      assignment e[0]: %s", a0);
            BTORLOG ("      assignment e[1]: %s", a1);
            btor_freestr (btor->mm, a0);
            btor_freestr (btor->mm, a1);
            BTORLOG ("      sls score e[0]: %f", s0);
            BTORLOG ("      sls score e[1]: %f", s1);
          }
#endif
          res = (s0 + s1) / 2.0;
          /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
             choose minimum (else it might again result in 1.0) */
          if (res == 1.0 && (s0 < 1.0 || s1 < 1.0)) res = s0 < s1 ? s0 : s1;
        }
      }
      else if (BTOR_IS_BV_EQ_NODE (real_cur))
      {
        bv0 = (BitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[0]);
        bv1 = (BitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[1]);
#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
        if (btor->options.loglevel.val)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[1]);
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
#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
        if (btor->options.loglevel.val)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[1]);
          BTORLOG ("      assignment e[0]: %s", a0);
          BTORLOG ("      assignment e[1]: %s", a1);
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
#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
        if (btor->options.loglevel.val)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, cur);
          BTORLOG ("      assignment : %s", a0);
          btor_freestr (btor->mm, a0);
        }
#endif
        res = ((BitVector *) btor_get_bv_model_aux (
                   btor, bv_model, fun_model, cur))
                  ->bits[0];
      }

      assert (!btor_find_in_ptr_hash_table (score, cur));
      b             = btor_insert_in_ptr_hash_table (score, cur);
      b->data.asDbl = res;

#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
      BTORLOG ("      sls score : %f", res);
#endif
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  BTOR_RELEASE_STACK (btor->mm, stack);

  assert (btor_find_in_ptr_hash_table (score, exp));
  assert (res == btor_find_in_ptr_hash_table (score, exp)->data.asDbl);
  return res;
}

static void
compute_sls_scores_aux (Btor *btor,
                        BtorPtrHashTable **bv_model,
                        BtorPtrHashTable **fun_model,
                        BtorPtrHashTable *score)
{
  assert (btor);
  assert (btor->sls_solver);
  assert (btor->sls_solver->roots);
  assert (bv_model);
  assert (fun_model);
  assert (check_id_table_mark_unset_dbg (btor));

  // TODO early pruning!!!
  //
  int i;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack stack, unmark_stack;
  BtorHashTableIterator it;

#ifdef BTOR_SLS_LOG_COMPUTE_SCORE
  BTORLOG ("");
  BTORLOG ("**** compute sls scores ***");
#endif

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  /* collect roots */
  init_node_hash_table_iterator (&it, btor->sls_solver->roots);
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
        BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[i]);
    }
    else
    {
      assert (real_cur->mark == 1);
      real_cur->mark = 2;
      if (!BTOR_IS_BV_EQ_NODE (real_cur) && !BTOR_IS_ULT_NODE (real_cur)
          && real_cur->len != 1)
        continue;
      compute_sls_score_node (btor, bv_model, fun_model, score, cur);
      compute_sls_score_node (
          btor, bv_model, fun_model, score, BTOR_INVERT_NODE (cur));
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
}

static void
compute_sls_scores (Btor *btor, BtorPtrHashTable *score)
{
  compute_sls_scores_aux (btor, &btor->bv_model, &btor->fun_model, score);
}

static double
compute_sls_score_formula (Btor *btor, BtorPtrHashTable *score)
{
  assert (btor);
  assert (score);

  int allsat;
  double res, sc, weight;
  BtorNode *root;
  BtorHashTableIterator it;

  res    = 0.0;
  allsat = 1;
  init_node_hash_table_iterator (&it, btor->sls_solver->roots);
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
select_candidate_constraint (Btor *btor, int nmoves)
{
  assert (btor);
  assert (btor->sls_solver);
  assert (btor->sls_solver->roots);
  assert (btor->sls_solver->score);

  int selected;
  double value, max_value, score;
  BtorNode *res, *cur;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b, *sb, *bucket;

  res       = 0;
  max_value = 0.0;
  bucket    = 0;
  init_hash_table_iterator (&it, btor->sls_solver->roots);
  while (has_next_node_hash_table_iterator (&it))
  {
    b   = it.bucket;
    cur = next_node_hash_table_iterator (&it);
    sb  = btor_find_in_ptr_hash_table (btor->sls_solver->score, cur);
    assert (sb);
    score = sb->data.asDbl;
    if (score >= 1.0) continue;
    if (!res)
    {
      res = cur;
      continue;
    }
    else
    {
      selected = b->data.asInt;
      value    = score + BTOR_SLS_SELECT_CFACT * sqrt (log (selected) / nmoves);
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
  BtorNode *cur, *real_cur, *e;
  BtorNodePtrStack stack, unmark_stack, controlling;
  const BitVector *bv;

  BTORLOG ("");
  BTORLOG ("*** select candidates");

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (controlling);

  BTOR_RESET_STACK (*candidates);

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
    if (btor->options.just.val && BTOR_IS_AND_NODE (real_cur)
        && real_cur->len == 1)
    {
      bv = btor_get_bv_model (btor, real_cur);
      if (!btor_is_zero_bv (bv)) /* push all */
        goto PUSH_CHILDREN;
      else /* push one controlling input */
      {
        BTOR_RESET_STACK (controlling);
        for (i = 0; i < real_cur->arity; i++)
        {
          e = real_cur->e[i];
          if (btor_is_zero_bv (btor_get_bv_model (btor, e)))
            BTOR_PUSH_STACK (btor->mm, controlling, real_cur->e[i]);
        }
        assert (BTOR_COUNT_STACK (controlling));
        BTOR_PUSH_STACK (
            btor->mm,
            stack,
            BTOR_PEEK_STACK (
                controlling,
                btor_pick_rand_rng (
                    &btor->rng, 0, BTOR_COUNT_STACK (controlling) - 1)));
      }
    }
    else if (btor->options.just.val && BTOR_IS_BCOND_NODE (real_cur))
    {
      BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[0]);
      bv = btor_get_bv_model (btor, real_cur->e[0]);
      if (btor_is_zero_bv (bv))
        BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[2]);
      else
        BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[1]);
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
  BTOR_RELEASE_STACK (btor->mm, controlling);
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

// TODO REMOVE AFTER MERGE WITH SLVENG (use public fun in btorhash)
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

// TODO REMOVE AFTER MERGE WITH SLVENG (use public fun in btorhash)
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
            BtorPtrHashTable *cans,
            BtorPtrHashTable *bv_model,
            BtorPtrHashTable *score)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (cans);
  assert (cans->count);
  assert (bv_model);
  assert (score);

  BtorNode *cur;
  BtorHashTableIterator it;
  BtorNodeIterator nit;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, unmark_stack;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  init_node_hash_table_iterator (&it, cans);
  while (has_next_node_hash_table_iterator (&it))
    BTOR_PUSH_STACK (btor->mm, stack, next_node_hash_table_iterator (&it));

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
    if ((b = btor_find_in_ptr_hash_table (score, cur)))
      btor_remove_from_ptr_hash_table (score, cur, 0, 0);
    if ((b = btor_find_in_ptr_hash_table (score, BTOR_INVERT_NODE (cur))))
      btor_remove_from_ptr_hash_table (score, BTOR_INVERT_NODE (cur), 0, 0);

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
             BtorPtrHashTable *cans,
             BtorPtrHashTable *score)
{
  assert (btor);
  assert (btor->sls_solver);
  assert (btor->sls_solver->roots);
  assert (bv_model);
  assert (*bv_model);
  assert (fun_model);
  assert (*fun_model);
  assert (cans);
  assert (cans->count);
  assert (score);

  BtorHashTableIterator it;
  BtorNode *exp;
  BitVector *ass;

  reset_cone (btor, cans, *bv_model, score);

  init_hash_table_iterator (&it, cans);
  while (has_next_node_hash_table_iterator (&it))
  {
    ass = it.bucket->data.asPtr;
    exp = next_node_hash_table_iterator (&it);
    btor_add_to_bv_model (btor, *bv_model, exp, ass);
  }

  btor_generate_model_aux (btor, *bv_model, *fun_model, 0);
  compute_sls_scores_aux (btor, bv_model, fun_model, score);
}

static inline void
update_assertion_weights (Btor *btor)
{
  assert (btor);
  assert (btor->sls_solver);
  assert (btor->sls_solver->roots);

  BtorNode *cur;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;

  if (!btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_SCORE_F))
  {
    /* decrease the weight of all satisfied assertions */
    init_node_hash_table_iterator (&it, btor->sls_solver->roots);
    while (has_next_node_hash_table_iterator (&it))
    {
      b   = it.bucket;
      cur = next_node_hash_table_iterator (&it);
      if (btor_find_in_ptr_hash_table (btor->sls_solver->score, cur)->data.asDbl
          == 0.0)
        continue;
      if (b->data.asInt > 1) b->data.asInt -= 1;
    }
  }
  else
  {
    /* increase the weight of all unsatisfied assertions */
    init_node_hash_table_iterator (&it, btor->sls_solver->roots);
    while (has_next_node_hash_table_iterator (&it))
    {
      b   = it.bucket;
      cur = next_node_hash_table_iterator (&it);
      if (btor_find_in_ptr_hash_table (btor->sls_solver->score, cur)->data.asDbl
          == 1.0)
        continue;
      b->data.asInt += 1;
    }
  }
}

static inline double
try_move (Btor *btor,
          BtorPtrHashTable **bv_model,
          BtorPtrHashTable *score,
          BtorPtrHashTable *cans)
{
  assert (btor);
  assert (btor->sls_solver);
  assert (btor->sls_solver->roots);
  assert (bv_model);
  assert (score);
  assert (cans);
  assert (cans->count);

  btor->sls_solver->stats.flips += 1;

#ifndef NBTORLOG
  char *a;
  BtorNode *can;
  BitVector *prev_ass, *new_ass;
  BtorHashTableIterator it;

  BTORLOG ("");
  BTORLOG ("  * try move:");
  init_hash_table_iterator (&it, cans);
  while (has_next_node_hash_table_iterator (&it))
  {
    new_ass  = it.bucket->data.asPtr;
    can      = next_node_hash_table_iterator (&it);
    prev_ass = (BitVector *) btor_get_bv_model (btor, can);
    BTORLOG ("      candidate: %s%s",
             BTOR_IS_REGULAR_NODE (can) ? "" : "-",
             node2string (can));
    a = btor_bv_to_char_bv (btor->mm, prev_ass);
    BTORLOG ("        prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char_bv (btor->mm, new_ass);
    BTORLOG ("        new   assignment: %s", a);
    btor_freestr (btor->mm, a);
  }
#endif

  /* we currently support QF_BV only, hence no funs */
  update_cone (btor, bv_model, &btor->fun_model, cans, score);

  return compute_sls_score_formula (btor, score);
}

static int
cmp_sls_moves_qsort (const void *move1, const void *move2)
{
  BtorSLSMove *m1, *m2;

  m1 = *((BtorSLSMove **) move1);
  m2 = *((BtorSLSMove **) move2);
  if (m1->sc > m2->sc) return 1;
  if (m1->sc < m2->sc) return -1;
  return 0;
}

#define BTOR_SLS_SELECT_MOVE_CHECK_SCORE(sc)                                   \
  do                                                                           \
  {                                                                            \
    done = (sc) == -1.0;                                                       \
    if (done                                                                   \
        || (btor->options.sls_strategy.val != BTOR_SLS_STRAT_PROB_RAND_WALK    \
            && ((sc) > btor->sls_solver->max_score                             \
                || (btor->options.sls_strategy.val                             \
                        == BTOR_SLS_STRAT_BEST_SAME_MOVE                       \
                    && (sc) == btor->sls_solver->max_score))))                 \
    {                                                                          \
      btor->sls_solver->max_score = (sc);                                      \
      btor->sls_solver->max_move  = mk;                                        \
      btor->sls_solver->max_gw    = gw;                                        \
      if (btor->sls_solver->max_cans->count)                                   \
      {                                                                        \
        init_node_hash_table_iterator (&it, btor->sls_solver->max_cans);       \
        while (has_next_node_hash_table_iterator (&it))                        \
        {                                                                      \
          assert (it.bucket->data.asPtr);                                      \
          btor_free_bv (btor->mm,                                              \
                        next_data_node_hash_table_iterator (&it)->asPtr);      \
        }                                                                      \
      }                                                                        \
      btor_delete_ptr_hash_table (btor->sls_solver->max_cans);                 \
      btor->sls_solver->max_cans = cans;                                       \
      if (done                                                                 \
          || btor->options.sls_strategy.val == BTOR_SLS_STRAT_FIRST_BEST_MOVE) \
        goto DONE;                                                             \
    }                                                                          \
    else if (btor->options.sls_strategy.val == BTOR_SLS_STRAT_PROB_RAND_WALK)  \
    {                                                                          \
      BTOR_NEW (btor->mm, m);                                                  \
      m->cans = cans;                                                          \
      m->sc   = (sc);                                                          \
      BTOR_PUSH_STACK (btor->mm, btor->sls_solver->moves, m);                  \
      btor->sls_solver->sum_score += (sc);                                     \
    }                                                                          \
    else                                                                       \
    {                                                                          \
      init_node_hash_table_iterator (&it, cans);                               \
      while (has_next_node_hash_table_iterator (&it))                          \
        btor_free_bv (btor->mm, next_data_hash_table_iterator (&it)->asPtr);   \
      btor_delete_ptr_hash_table (cans);                                       \
    }                                                                          \
  } while (0)

static inline int
select_inc_dec_not_move (Btor *btor,
                         BitVector *(*fun) (BtorMemMgr *, BitVector *),
                         BtorNodePtrStack *candidates,
                         int gw)
{
  double sc;
  int i, done = 0;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;

  if (fun == btor_inc_bv)
    mk = BTOR_SLS_MOVE_INC;
  else if (fun == btor_dec_bv)
    mk = BTOR_SLS_MOVE_DEC;
  else
  {
    assert (fun == btor_not_bv);
    mk = BTOR_SLS_MOVE_NOT;
  }

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, btor->sls_solver->score, same_node, data_as_double, 0, 0);

  cans = btor_new_ptr_hash_table (btor->mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);

  for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
  {
    can = BTOR_PEEK_STACK (*candidates, i);
    assert (can);

    ass = (BitVector *) btor_get_bv_model (btor, can);
    assert (ass);

    b         = btor_find_in_ptr_hash_table (btor->sls_solver->max_cans, can);
    max_neigh = b ? b->data.asPtr : 0;

    b             = btor_insert_in_ptr_hash_table (cans, can);
    b->data.asPtr = btor->options.sls_move_inc_move_test.val && max_neigh
                        ? fun (btor->mm, max_neigh)
                        : fun (btor->mm, ass);
  }

  sc = try_move (btor, &bv_model, score, cans);
  BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);

DONE:
  btor_delete_bv_model (btor, &bv_model);
  btor_delete_ptr_hash_table (score);
  return done;
}

static inline int
select_flip_move (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  double sc;
  int i, pos, cpos, n_endpos, done = 0;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;

  mk = BTOR_SLS_MOVE_FLIP;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, btor->sls_solver->score, same_node, data_as_double, 0, 0);

  for (pos = 0, n_endpos = 0; n_endpos < BTOR_COUNT_STACK (*candidates); pos++)
  {
    cans = btor_new_ptr_hash_table (btor->mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

    for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
    {
      can = BTOR_PEEK_STACK (*candidates, i);
      assert (can);

      ass = (BitVector *) btor_get_bv_model (btor, can);
      assert (ass);

      b         = btor_find_in_ptr_hash_table (btor->sls_solver->max_cans, can);
      max_neigh = b ? b->data.asPtr : 0;

      if (pos == ass->width - 1) n_endpos += 1;
      cpos = pos % ass->width;

      b             = btor_insert_in_ptr_hash_table (cans, can);
      b->data.asPtr = btor->options.sls_move_inc_move_test.val && max_neigh
                          ? btor_flipped_bit_bv (btor->mm, max_neigh, cpos)
                          : btor_flipped_bit_bv (btor->mm, ass, cpos);
    }

    sc = try_move (btor, &bv_model, score, cans);
    BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);
  }

DONE:
  btor_delete_bv_model (btor, &bv_model);
  btor_delete_ptr_hash_table (score);
  return done;
}

static inline int
select_flip_range_move (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  double sc;
  int i, up, cup, clo, n_endpos, done = 0;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;

  mk = BTOR_SLS_MOVE_FLIP_RANGE;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, btor->sls_solver->score, same_node, data_as_double, 0, 0);

  for (up = 1, n_endpos = 0; n_endpos < BTOR_COUNT_STACK (*candidates);
       up = 2 * up + 1)
  {
    cans = btor_new_ptr_hash_table (btor->mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

    for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
    {
      can = BTOR_PEEK_STACK (*candidates, i);
      assert (can);

      ass = (BitVector *) btor_get_bv_model (btor, can);
      assert (ass);

      b         = btor_find_in_ptr_hash_table (btor->sls_solver->max_cans, can);
      max_neigh = b ? b->data.asPtr : 0;

      clo = 0;
      cup = up;
      if (up >= ass->width)
      {
        if ((up - 1) / 2 < ass->width) n_endpos += 1;
        cup = ass->width - 1;
      }

      b = btor_insert_in_ptr_hash_table (cans, can);

      /* range from LSB rather than MSB with given prob */
      if (btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_RANGE_LSB_VS_MSB))
      {
        clo = ass->width - 1 - cup;
        cup = ass->width - 1;
      }

      b->data.asPtr =
          btor->options.sls_move_inc_move_test.val && max_neigh
              ? btor_flipped_bit_range_bv (btor->mm, max_neigh, cup, clo)
              : btor_flipped_bit_range_bv (btor->mm, ass, cup, clo);
    }

    sc = try_move (btor, &bv_model, score, cans);
    BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);
  }

DONE:
  btor_delete_bv_model (btor, &bv_model);
  btor_delete_ptr_hash_table (score);
  return done;
}

static inline int
select_flip_segment_move (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  double sc;
  int i, lo, clo, up, cup, ctmp, seg, n_endpos, done = 0;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;

  mk = BTOR_SLS_MOVE_FLIP_SEGMENT;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, btor->sls_solver->score, same_node, data_as_double, 0, 0);

  for (seg = 2; seg <= 8; seg <<= 1)
  {
    for (lo = 0, up = seg - 1, n_endpos = 0;
         n_endpos < BTOR_COUNT_STACK (*candidates);
         lo += seg, up += seg)
    {
      cans = btor_new_ptr_hash_table (btor->mm,
                                      (BtorHashPtr) btor_hash_exp_by_id,
                                      (BtorCmpPtr) btor_compare_exp_by_id);

      for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
      {
        can = BTOR_PEEK_STACK (*candidates, i);
        assert (can);

        ass = (BitVector *) btor_get_bv_model (btor, can);
        assert (ass);

        b = btor_find_in_ptr_hash_table (btor->sls_solver->max_cans, can);
        max_neigh = b ? b->data.asPtr : 0;

        clo = lo;
        cup = up;

        if (up >= ass->width)
        {
          if (up - seg < ass->width) n_endpos += 1;
          cup = ass->width - 1;
        }

        if (lo >= ass->width - 1) clo = ass->width < seg ? 0 : ass->width - seg;

        b = btor_insert_in_ptr_hash_table (cans, can);

        /* range from LSB rather than MSB with given prob */
        if (btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_SEG_LSB_VS_MSB))
        {
          ctmp = clo;
          clo  = ass->width - 1 - cup;
          cup  = ass->width - 1 - ctmp;
        }

        b->data.asPtr =
            btor->options.sls_move_inc_move_test.val && max_neigh
                ? btor_flipped_bit_range_bv (btor->mm, max_neigh, cup, clo)
                : btor_flipped_bit_range_bv (btor->mm, ass, cup, clo);
      }

      sc = try_move (btor, &bv_model, score, cans);
      BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);
    }
  }

DONE:
  btor_delete_bv_model (btor, &bv_model);
  btor_delete_ptr_hash_table (score);
  return done;
}

static inline int
select_rand_range_move (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  double sc, rand_max_score = -1.0;
  int i, up, cup, n_endpos, done = 0;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BitVector *ass;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;

  mk = BTOR_SLS_MOVE_RAND;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, btor->sls_solver->score, same_node, data_as_double, 0, 0);

  for (up = 1, n_endpos = 0; n_endpos < BTOR_COUNT_STACK (*candidates);
       up = 2 * up + 1)
  {
    cans = btor_new_ptr_hash_table (btor->mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

    for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
    {
      can = BTOR_PEEK_STACK (*candidates, i);
      assert (can);

      ass = (BitVector *) btor_get_bv_model (btor, can);
      assert (ass);

      cup = up;

      if (up >= ass->width)
      {
        if ((up - 1) / 2 < ass->width) n_endpos += 1;
        cup = ass->width - 1;
      }

      btor_insert_in_ptr_hash_table (cans, can)->data.asPtr =
          btor_new_random_range_bv (btor->mm, &btor->rng, ass->width, cup, 0);
    }

    sc = try_move (btor, &bv_model, score, cans);
    if (rand_max_score == -1.0 || sc > rand_max_score)
    {
      /* reset, use current */
      btor->sls_solver->max_score = -1.0;
      rand_max_score              = sc;
    }
    BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);
  }

DONE:
  btor_delete_bv_model (btor, &bv_model);
  btor_delete_ptr_hash_table (score);
  return done;
}

static inline int
select_move_aux (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  assert (btor);
  assert (candidates);
  assert (gw >= 0);

  BtorSLSMoveKind mk;
  int done;

  for (mk = 0, done = 0; mk < BTOR_SLS_MOVE_DONE; mk++)
  {
    switch (mk)
    {
      case BTOR_SLS_MOVE_INC:
        if ((done =
                 select_inc_dec_not_move (btor, btor_inc_bv, candidates, gw)))
          return done;
        break;

      case BTOR_SLS_MOVE_DEC:
        if ((done =
                 select_inc_dec_not_move (btor, btor_dec_bv, candidates, gw)))
          return done;
        break;

      case BTOR_SLS_MOVE_NOT:
        if ((done =
                 select_inc_dec_not_move (btor, btor_not_bv, candidates, gw)))
          return done;
        break;

      case BTOR_SLS_MOVE_FLIP_RANGE:
        if (!btor->options.sls_move_range.val) continue;
        if ((done = select_flip_range_move (btor, candidates, gw))) return done;
        break;

      case BTOR_SLS_MOVE_FLIP_SEGMENT:
        if (!btor->options.sls_move_segment.val) continue;
        if ((done = select_flip_segment_move (btor, candidates, gw)))
          return done;
        break;

      default:
        assert (mk == BTOR_SLS_MOVE_FLIP);
        if ((done = select_flip_move (btor, candidates, gw))) return done;
    }
  }

  return done;
}

static inline void
select_move (Btor *btor, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (btor->sls_solver->max_cans);
  assert (!btor->sls_solver->max_cans->count);
  assert (candidates);

  int i, r, done, randomizeall;
  double rd, sum;
  BtorNode *can;
  BitVector *neigh;
  BtorNodePtrStack cans;
  BtorSLSMove *m;
  BtorHashTableIterator it;

  BTOR_INIT_STACK (cans);
  /* one after another */
  for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
  {
    can = BTOR_PEEK_STACK (*candidates, i);
    assert (can);
    BTOR_PUSH_STACK (btor->mm, cans, can);

    if ((done = select_move_aux (btor, &cans, 0))) goto DONE;

    BTOR_RESET_STACK (cans);
  }

  /* groupwise */
  if (btor->options.sls_move_gw.val && BTOR_COUNT_STACK (*candidates) > 1)
  {
    if ((done = select_move_aux (btor, candidates, 1))) goto DONE;
  }

  /* select probabilistic random walk move */
  if (btor->options.sls_strategy.val == BTOR_SLS_STRAT_PROB_RAND_WALK)
  {
    assert (btor->sls_solver->max_cans->count == 0);
    assert (BTOR_COUNT_STACK (btor->sls_solver->moves));

    qsort (btor->sls_solver->moves.start,
           BTOR_COUNT_STACK (btor->sls_solver->moves),
           sizeof (BtorSLSMove *),
           cmp_sls_moves_qsort);

    rd  = btor_pick_rand_dbl_rng (&btor->rng, 0, btor->sls_solver->sum_score);
    m   = BTOR_PEEK_STACK (btor->sls_solver->moves, 0);
    sum = m->sc;
    //      printf ("sumscore: %f r: %f sum: %f\n",
    //	      btor->sls_solver->sum_score, rd, sum);
    for (i = 0; i < BTOR_COUNT_STACK (btor->sls_solver->moves); i++)
    {
      sum += BTOR_PEEK_STACK (btor->sls_solver->moves, i)->sc;
      if (sum > rd) break;
      m = BTOR_PEEK_STACK (btor->sls_solver->moves, i);
    }
    //      printf ("sum: %f\n", sum);

    btor->sls_solver->max_gw   = m->cans->count > 1;
    btor->sls_solver->max_move = BTOR_SLS_MOVE_RAND_WALK;
    init_node_hash_table_iterator (&it, m->cans);
    while (has_next_node_hash_table_iterator (&it))
    {
      neigh = btor_copy_bv (btor->mm, it.bucket->data.asPtr);
      assert (neigh);
      can = next_node_hash_table_iterator (&it);
      btor_insert_in_ptr_hash_table (btor->sls_solver->max_cans, can)
          ->data.asPtr = neigh;
    }
  }

  if (btor->sls_solver->max_cans->count == 0)
  {
    assert (btor->sls_solver->max_move == BTOR_SLS_MOVE_DONE);

    /* randomize if no best move was found */
    BTORLOG ("--- randomized");
    randomizeall =
        btor->options.sls_move_rand_all.val
            ? btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_RAND_ALL_VS_ONE)
            : 0;

    if (randomizeall)
    {
      btor->sls_solver->max_gw   = 1;
      btor->sls_solver->max_move = BTOR_SLS_MOVE_RAND;

      for (r = 0; r < BTOR_COUNT_STACK (*candidates) - 1; r++)
      {
        can = BTOR_PEEK_STACK (*candidates, r);
        if (BTOR_REAL_ADDR_NODE (can)->len == 1)
          neigh = btor_flipped_bit_bv (
              btor->mm, (BitVector *) btor_get_bv_model (btor, can), 0);
        else
          neigh = btor_new_random_bv (btor->mm, &btor->rng, can->len);

        btor_insert_in_ptr_hash_table (btor->sls_solver->max_cans, can)
            ->data.asPtr = neigh;
      }
    }
    else
    {
      btor->sls_solver->max_gw   = 0;
      btor->sls_solver->max_move = BTOR_SLS_MOVE_RAND;

      can = BTOR_PEEK_STACK (
          *candidates,
          btor_pick_rand_rng (
              &btor->rng, 0, BTOR_COUNT_STACK (*candidates) - 1));

      if (BTOR_REAL_ADDR_NODE (can)->len == 1)
      {
        neigh = btor_flipped_bit_bv (
            btor->mm, (BitVector *) btor_get_bv_model (btor, can), 0);
        btor_insert_in_ptr_hash_table (btor->sls_solver->max_cans, can)
            ->data.asPtr = neigh;
      }
      /* pick neighbor with randomized bit range (best guess) */
      else if (btor->options.sls_move_rand_range.val)
      {
        select_rand_range_move (btor, &cans, 0);
        assert (btor->sls_solver->max_cans->count == 1);
        assert (btor->sls_solver->max_cans->first->key == can);
      }
      else
      {
        neigh = btor_new_random_bv (btor->mm, &btor->rng, can->len);
        btor_insert_in_ptr_hash_table (btor->sls_solver->max_cans, can)
            ->data.asPtr = neigh;
      }

      assert (!btor->sls_solver->max_gw);
      assert (btor->sls_solver->max_move == BTOR_SLS_MOVE_RAND);
    }
  }

DONE:
  BTOR_RELEASE_STACK (btor->mm, cans);
  while (!BTOR_EMPTY_STACK (btor->sls_solver->moves))
  {
    m = BTOR_POP_STACK (btor->sls_solver->moves);
    init_node_hash_table_iterator (&it, m->cans);
    while (has_next_node_hash_table_iterator (&it))
      btor_free_bv (btor->mm, next_data_hash_table_iterator (&it)->asPtr);
    btor_delete_ptr_hash_table (m->cans);
    BTOR_DELETE (btor->mm, m);
  }
}

static inline void
select_random_move (Btor *btor, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (btor->sls_solver->max_cans);
  assert (!btor->sls_solver->max_cans->count);
  assert (candidates);

  int i, r, up, lo;
  BtorSLSMoveKind mk;
  BtorNodePtrStack cans, *pcans;
  BtorNode *can;
  BitVector *ass, *neigh;
  BtorPtrHashTable *max_cans;

  BTOR_INIT_STACK (cans);

  max_cans                   = btor->sls_solver->max_cans;
  btor->sls_solver->max_move = BTOR_SLS_MOVE_RAND_WALK;

  /* select candidate(s) */
  if (btor->options.sls_move_gw.val
      && !btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_SINGLE_VS_GW))
  {
    pcans                    = candidates;
    btor->sls_solver->max_gw = 1;
  }
  else
  {
    BTOR_PUSH_STACK (
        btor->mm,
        cans,
        BTOR_PEEK_STACK (
            *candidates,
            btor_pick_rand_rng (
                &btor->rng, 0, BTOR_COUNT_STACK (*candidates) - 1)));
    pcans                    = &cans;
    btor->sls_solver->max_gw = 0;
  }

  /* select neighbor(s) */
  for (i = 0; i < BTOR_COUNT_STACK (*pcans); i++)
  {
    can = BTOR_PEEK_STACK ((*pcans), i);
    ass = (BitVector *) btor_get_bv_model (btor, can);
    assert (ass);

    r = btor_pick_rand_rng (
        &btor->rng, 0, BTOR_SLS_MOVE_DONE - 1 + ass->width - 1);

    if (r < ass->width)
      mk = BTOR_SLS_MOVE_FLIP;
    else
      mk = (BtorSLSMoveKind) r - ass->width + 1;
    assert (mk >= 0);

    if ((!btor->options.sls_move_segment.val
         && mk == BTOR_SLS_MOVE_FLIP_SEGMENT)
        || (!btor->options.sls_move_range.val
            && mk == BTOR_SLS_MOVE_FLIP_RANGE))
    {
      mk = BTOR_SLS_MOVE_FLIP;
    }

    switch (mk)
    {
      case BTOR_SLS_MOVE_INC: neigh = btor_inc_bv (btor->mm, ass); break;
      case BTOR_SLS_MOVE_DEC: neigh = btor_dec_bv (btor->mm, ass); break;
      case BTOR_SLS_MOVE_NOT: neigh = btor_not_bv (btor->mm, ass); break;
      case BTOR_SLS_MOVE_FLIP_RANGE:
        up = btor_pick_rand_rng (
            &btor->rng, ass->width > 1 ? 1 : 0, ass->width - 1);
        neigh = btor_flipped_bit_range_bv (btor->mm, ass, up, 0);
        break;
      case BTOR_SLS_MOVE_FLIP_SEGMENT:
        lo = btor_pick_rand_rng (&btor->rng, 0, ass->width - 1);
        up = btor_pick_rand_rng (
            &btor->rng, lo < ass->width - 1 ? lo + 1 : lo, ass->width - 1);
        neigh = btor_flipped_bit_range_bv (btor->mm, ass, up, lo);
        break;
      default:
        assert (mk == BTOR_SLS_MOVE_FLIP);
        neigh = btor_flipped_bit_bv (
            btor->mm, ass, btor_pick_rand_rng (&btor->rng, 0, ass->width - 1));
        break;
    }

    btor_insert_in_ptr_hash_table (max_cans, can)->data.asPtr = neigh;
  }

  BTOR_RELEASE_STACK (btor->mm, cans);
}

static void
move (Btor *btor, int nmoves)
{
  assert (btor);
  assert (!btor->sls_solver->max_cans);
  assert (compute_sls_score_formula (btor, btor->sls_solver->score) != -1.0);

  BtorNodePtrStack candidates;
  BtorHashTableIterator it;

  BTORLOG ("");
  BTORLOG ("*** move");

  BTOR_INIT_STACK (candidates);

  select_candidates (
      btor, select_candidate_constraint (btor, nmoves), &candidates);
  assert (BTOR_COUNT_STACK (candidates));

  btor->sls_solver->max_cans =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->sls_solver->max_score =
      compute_sls_score_formula (btor, btor->sls_solver->score);
  btor->sls_solver->max_move = BTOR_SLS_MOVE_DONE;
  btor->sls_solver->max_gw   = -1;

  if (btor->options.sls_move_rand_walk.val
      && !btor_pick_rand_rng (
             &btor->rng, 0, btor->options.sls_move_rand_walk_prob.val))
    select_random_move (btor, &candidates);
  else
    select_move (btor, &candidates);

  assert (btor->sls_solver->max_cans->count);
  assert (btor->sls_solver->max_move != BTOR_SLS_MOVE_DONE);

#ifndef NBTORLOG
  BTORLOG ("");
  BTORLOG (" * move");
  char *a;
  BtorNode *can;
  BitVector *neigh, *ass;
  init_node_hash_table_iterator (&it, btor->sls_solver->max_cans);
  while (has_next_node_hash_table_iterator (&it))
  {
    neigh = it.bucket->data.asPtr;
    can   = next_node_hash_table_iterator (&it);
    ass   = (BitVector *) btor_get_bv_model (btor, can);
    a     = btor_bv_to_char_bv (btor->mm, ass);
    BTORLOG ("  candidate: %s%s",
             BTOR_IS_REGULAR_NODE (can) ? "" : "-",
             node2string (can));
    BTORLOG ("  prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char_bv (btor->mm, neigh);
    BTORLOG ("  new   assignment: %s", a);
    btor_freestr (btor->mm, a);
  }
#endif

  update_cone (btor,
               &btor->bv_model,
               &btor->fun_model,
               btor->sls_solver->max_cans,
               btor->sls_solver->score);

  btor->sls_solver->stats.moves += 1;

  assert (btor->sls_solver->max_move != BTOR_SLS_MOVE_DONE);
  assert (btor->sls_solver->max_gw >= 0);

  switch (btor->sls_solver->max_move)
  {
    case BTOR_SLS_MOVE_FLIP:
      if (!btor->sls_solver->max_gw)
        btor->sls_solver->stats.move_flip += 1;
      else
        btor->sls_solver->stats.move_gw_flip += 1;
      break;
    case BTOR_SLS_MOVE_INC:
      if (!btor->sls_solver->max_gw)
        btor->sls_solver->stats.move_inc += 1;
      else
        btor->sls_solver->stats.move_gw_inc += 1;
      break;
    case BTOR_SLS_MOVE_DEC:
      if (!btor->sls_solver->max_gw)
        btor->sls_solver->stats.move_dec += 1;
      else
        btor->sls_solver->stats.move_gw_dec += 1;
      break;
    case BTOR_SLS_MOVE_NOT:
      if (!btor->sls_solver->max_gw)
        btor->sls_solver->stats.move_not += 1;
      else
        btor->sls_solver->stats.move_gw_not += 1;
      break;
    case BTOR_SLS_MOVE_FLIP_RANGE:
      if (!btor->sls_solver->max_gw)
        btor->sls_solver->stats.move_range += 1;
      else
        btor->sls_solver->stats.move_gw_range += 1;
      break;
    case BTOR_SLS_MOVE_FLIP_SEGMENT:
      if (!btor->sls_solver->max_gw)
        btor->sls_solver->stats.move_seg += 1;
      else
        btor->sls_solver->stats.move_gw_seg += 1;
      break;
    case BTOR_SLS_MOVE_RAND:
      if (!btor->sls_solver->max_gw)
        btor->sls_solver->stats.move_rand += 1;
      else
        btor->sls_solver->stats.move_gw_rand += 1;
      break;
    default:
      assert (btor->sls_solver->max_move == BTOR_SLS_MOVE_RAND_WALK);
      if (!btor->sls_solver->max_gw)
        btor->sls_solver->stats.move_rand_walk += 1;
      else
        btor->sls_solver->stats.move_gw_rand_walk += 1;
  }

  if (btor->sls_solver->max_move == BTOR_SLS_MOVE_RAND)
    update_assertion_weights (btor);

  /** cleanup **/
  init_node_hash_table_iterator (&it, btor->sls_solver->max_cans);
  while (has_next_node_hash_table_iterator (&it))
    btor_free_bv (btor->mm, next_data_hash_table_iterator (&it)->asPtr);
  btor_delete_ptr_hash_table (btor->sls_solver->max_cans);
  btor->sls_solver->max_cans = 0;
  BTOR_RELEASE_STACK (btor->mm, candidates);
}

/* Note: failed assumptions -> no handling necessary, sls only works for SAT */
int
btor_sat_aux_btor_sls (Btor *btor)
{
  assert (btor);

  int i, j, max_steps;
  int sat_result;
  int nmoves;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;

  if (!btor->sls_solver) btor->sls_solver = btor_new_sls_solver (btor);

  nmoves = 0;

  //#ifndef NDEBUG
  //  Btor *clone = btor_clone_exp_layer (btor, 0, 0);
  //  clone->options.sls.val = 0;
  //  clone->options.auto_cleanup.val = 1;
  //  clone->options.auto_cleanup_internal.val = 1;
  //  clone->options.loglevel.val = 0;
  //  clone->options.verbosity.val = 0;
  //  clone->options.model_gen.val = 1;
  //  clone->options.beta_reduce_all.val = 1;
  //  int csat_result = btor_sat_btor (clone, -1, -1);
  //  if (csat_result == BTOR_UNSAT) goto UNSAT;
  //  assert (!clone->lambdas->count && !clone->ufs->count);
  //  printf ("clone sat\n");
  //  btor_delete_btor (clone);
  //#endif
  //
  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  sat_result = btor_simplify (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->ufs->count != 0
          || (!btor->options.beta_reduce_all.val && btor->lambdas->count != 0),
      "sls engine supports QF_BV only");
  btor_update_assumptions (btor);

  if (btor->inconsistent) goto UNSAT;

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  btor_generate_model_sls (btor, 0, 1);

  /* collect roots */
  assert (!btor->sls_solver->roots);
  btor->sls_solver->roots =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  assert (btor->synthesized_constraints->count == 0);
  init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  queue_node_hash_table_iterator (&it, btor->assumptions);
  while (has_next_node_hash_table_iterator (&it))
  {
    b             = btor_insert_in_ptr_hash_table (btor->sls_solver->roots,
                                       next_node_hash_table_iterator (&it));
    b->data.asInt = 1; /* initial assertion weight */
  }

  if (!btor->sls_solver->score)
    btor->sls_solver->score =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

  i = 1;
  for (;;)
  {
    /* compute initial sls score */
    compute_sls_scores (btor, btor->sls_solver->score);

    if (compute_sls_score_formula (btor, btor->sls_solver->score) == -1.0)
    {
      sat_result = BTOR_SAT;
      goto SAT;
    }

    for (j = 0, max_steps = BTOR_SLS_MAXSTEPS (i);
         j < max_steps;  //|| btor->options.sls_move_prob_rand_walk.val;
         j++)
    {
      move (btor, nmoves++);

      if (compute_sls_score_formula (btor, btor->sls_solver->score) == -1.0)
      {
        sat_result = BTOR_SAT;
        goto SAT;
      }
    }

    /* restart */
    btor_generate_model_sls (btor, 0, 1);
    btor_delete_ptr_hash_table (btor->sls_solver->score);
    btor->sls_solver->score =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    i += 1;
  }

SAT:
  assert (sat_result == BTOR_SAT);
  btor->sls_solver->stats.restarts = i - 1;
  assert (btor->sls_solver->stats.moves == nmoves);
  goto DONE;

UNSAT:
  sat_result = BTOR_UNSAT;

DONE:
  if (btor->sls_solver->roots)
  {
    btor_delete_ptr_hash_table (btor->sls_solver->roots);
    btor->sls_solver->roots = 0;
  }
  btor->last_sat_result = sat_result;
  return sat_result;
}

void
btor_generate_model_sls (Btor *btor, int model_for_all_nodes, int reset)
{
  assert (btor);

  if (!reset && btor->bv_model) return;
  btor_init_bv_model (btor, &btor->bv_model);
  btor_init_fun_model (btor, &btor->fun_model);
  btor_generate_model_aux (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

BtorSLSSolver *
btor_new_sls_solver (Btor *btor)
{
  assert (btor);

  BtorSLSSolver *slv;

  BTOR_CNEW (btor->mm, slv);
  slv->btor = btor;
  return slv;
}

BtorSLSSolver *
btor_clone_sls_solver (Btor *clone, BtorSLSSolver *slv, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (slv);
  assert (exp_map);

  int i;
  BtorSLSSolver *res;
  BtorSLSMove *m, *cm;

  BTOR_CNEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorSLSSolver));
  res->btor  = clone;
  res->roots = btor_clone_ptr_hash_table (clone->mm,
                                          slv->roots,
                                          btor_clone_key_as_node,
                                          btor_clone_data_as_int,
                                          exp_map,
                                          0);
  res->score = btor_clone_ptr_hash_table (clone->mm,
                                          slv->score,
                                          btor_clone_key_as_node,
                                          btor_clone_data_as_dbl,
                                          exp_map,
                                          0);

  BTOR_INIT_STACK (res->moves);
  assert (BTOR_SIZE_STACK (slv->moves) || !BTOR_COUNT_STACK (slv->moves));
  if (BTOR_SIZE_STACK (slv->moves))
  {
    BTOR_NEWN (clone->mm, res->moves.start, BTOR_SIZE_STACK (slv->moves));
    res->moves.top = res->moves.start;
    res->moves.end = res->moves.start + BTOR_SIZE_STACK (slv->moves);

    for (i = 0; i < BTOR_COUNT_STACK (slv->moves); i++)
    {
      m = BTOR_PEEK_STACK (slv->moves, i);
      assert (m);
      BTOR_NEW (clone->mm, cm);
      cm->cans = btor_clone_ptr_hash_table (clone->mm,
                                            m->cans,
                                            btor_clone_key_as_node,
                                            btor_clone_data_as_bv_ptr,
                                            exp_map,
                                            0);
      cm->sc   = m->sc;
      BTOR_PUSH_STACK (clone->mm, res->moves, m);
    }
  }
  assert (BTOR_COUNT_STACK (slv->moves) == BTOR_COUNT_STACK (res->moves));
  assert (BTOR_SIZE_STACK (slv->moves) == BTOR_SIZE_STACK (res->moves));

  res->max_cans = btor_clone_ptr_hash_table (clone->mm,
                                             slv->max_cans,
                                             btor_clone_key_as_node,
                                             btor_clone_data_as_bv_ptr,
                                             exp_map,
                                             0);

  return res;
}

void
btor_delete_sls_solver (Btor *btor, BtorSLSSolver *slv)
{
  assert (slv);

  BtorHashTableIterator it;
  BtorSLSMove *m;

  if (slv->score) btor_delete_ptr_hash_table (slv->score);
  if (slv->roots) btor_delete_ptr_hash_table (slv->roots);
  while (!BTOR_EMPTY_STACK (slv->moves))
  {
    m = BTOR_POP_STACK (slv->moves);
    init_node_hash_table_iterator (&it, m->cans);
    while (has_next_node_hash_table_iterator (&it))
      btor_free_bv (btor->mm, next_data_hash_table_iterator (&it)->asPtr);
    btor_delete_ptr_hash_table (m->cans);
  }
  BTOR_RELEASE_STACK (btor->mm, slv->moves);
  if (slv->max_cans)
  {
    init_node_hash_table_iterator (&it, slv->max_cans);
    while (has_next_node_hash_table_iterator (&it))
      btor_free_bv (btor->mm, next_data_hash_table_iterator (&it)->asPtr);
    btor_delete_ptr_hash_table (slv->max_cans);
  }
  BTOR_DELETE (btor->mm, slv);
}

void
btor_print_stats_sls_solver (Btor *btor, BtorSLSSolver *slv)
{
  assert (btor);
  assert (slv);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "sls restarts: %d", btor->sls_solver->stats.restarts);
  BTOR_MSG (btor->msg, 1, "sls moves: %d", btor->sls_solver->stats.moves);
  BTOR_MSG (btor->msg, 1, "sls flips: %d", btor->sls_solver->stats.flips);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "sls flip        moves: %d",
            btor->sls_solver->stats.move_flip);
  BTOR_MSG (btor->msg,
            1,
            "sls inc         moves: %d",
            btor->sls_solver->stats.move_inc);
  BTOR_MSG (btor->msg,
            1,
            "sls dec         moves: %d",
            btor->sls_solver->stats.move_dec);
  BTOR_MSG (btor->msg,
            1,
            "sls not         moves: %d",
            btor->sls_solver->stats.move_not);
  BTOR_MSG (btor->msg,
            1,
            "sls range       moves: %d",
            btor->sls_solver->stats.move_range);
  BTOR_MSG (btor->msg,
            1,
            "sls segment     moves: %d",
            btor->sls_solver->stats.move_seg);
  BTOR_MSG (btor->msg,
            1,
            "sls random      moves: %d",
            btor->sls_solver->stats.move_rand);
  BTOR_MSG (btor->msg,
            1,
            "sls random walk moves: %d",
            btor->sls_solver->stats.move_rand_walk);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "sls gw flip        moves: %d",
            btor->sls_solver->stats.move_gw_flip);
  BTOR_MSG (btor->msg,
            1,
            "sls gw inc         moves: %d",
            btor->sls_solver->stats.move_gw_inc);
  BTOR_MSG (btor->msg,
            1,
            "sls gw dec         moves: %d",
            btor->sls_solver->stats.move_gw_dec);
  BTOR_MSG (btor->msg,
            1,
            "sls gw not         moves: %d",
            btor->sls_solver->stats.move_gw_not);
  BTOR_MSG (btor->msg,
            1,
            "sls gw range       moves: %d",
            btor->sls_solver->stats.move_gw_range);
  BTOR_MSG (btor->msg,
            1,
            "sls gw segment     moves: %d",
            btor->sls_solver->stats.move_gw_seg);
  BTOR_MSG (btor->msg,
            1,
            "sls gw random      moves: %d",
            btor->sls_solver->stats.move_gw_rand);
  BTOR_MSG (btor->msg,
            1,
            "sls gw random walk moves: %d",
            btor->sls_solver->stats.move_gw_rand_walk);
}

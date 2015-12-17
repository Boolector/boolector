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
#include "utils/btorhashptr.h"
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
/* start ranges from MSB rather than LSB */
#define BTOR_SLS_PROB_RANGE_MSB_VS_LSB 1
/* start segments from MSB rather than LSB */
#define BTOR_SLS_PROB_SEG_MSB_VS_LSB 1

/*------------------------------------------------------------------------*/

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
                        BtorPtrHashTable **bv_model,
                        BtorPtrHashTable **fun_model,
                        BtorPtrHashTable *score,
                        BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score);
  assert (btor_check_id_table_aux_mark_unset_dbg (btor));
  assert (exp);

  int i;
  double res, s0, s1;
  BtorNode *cur, *real_cur;
  BtorBitVector *bv0, *bv1;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, unmark_stack;
#ifndef NBTORLOG
  char *a0, *a1;
#endif

  res = 0.0;
  assert (BTOR_IS_BV_EQ_NODE (BTOR_REAL_ADDR_NODE (exp))
          || BTOR_IS_ULT_NODE (BTOR_REAL_ADDR_NODE (exp))
          || btor_get_exp_width (btor, exp) == 1);

  if ((b = btor_get_ptr_hash_table (score, exp))) return b->data.as_dbl;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  BTOR_PUSH_STACK (btor->mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->aux_mark == 2 || btor_get_ptr_hash_table (score, cur))
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
          && btor_get_exp_width (btor, real_cur) != 1)
        continue;

      BTORLOG (3, "");
      BTORLOG (3,
               "*** compute sls score for: %s(%s)",
               BTOR_IS_INVERTED_NODE (cur) ? "-" : " ",
               node2string (cur));

      if (BTOR_IS_AND_NODE (real_cur))
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
          if (btor->options.loglevel.val >= 2)
          {
            a0 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, BTOR_INVERT_NODE (real_cur->e[0]));
            a1 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, BTOR_INVERT_NODE (real_cur->e[1]));
            BTORLOG (3, "      assignment e[0]: %s", a0);
            BTORLOG (3, "      assignment e[1]: %s", a1);
            btor_freestr (btor->mm, a0);
            btor_freestr (btor->mm, a1);
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
          if (btor->options.loglevel.val >= 2)
          {
            a0 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, real_cur->e[0]);
            a1 = (char *) btor_get_bv_model_str_aux (
                btor, bv_model, fun_model, real_cur->e[1]);
            BTORLOG (3, "      assignment e[0]: %s", a0);
            BTORLOG (3, "      assignment e[1]: %s", a1);
            btor_freestr (btor->mm, a0);
            btor_freestr (btor->mm, a1);
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
      else if (BTOR_IS_BV_EQ_NODE (real_cur))
      {
        bv0 = (BtorBitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[0]);
        bv1 = (BtorBitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[1]);
#ifndef NBTORLOG
        if (btor->options.loglevel.val >= 2)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[1]);
          BTORLOG (3, "      assignment e[0]: %s", a0);
          BTORLOG (3, "      assignment e[1]: %s", a1);
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
        bv0 = (BtorBitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[0]);
        bv1 = (BtorBitVector *) btor_get_bv_model_aux (
            btor, bv_model, fun_model, real_cur->e[1]);
#ifndef NBTORLOG
        if (btor->options.loglevel.val >= 2)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[0]);
          a1 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, real_cur->e[1]);
          BTORLOG (3, "      assignment e[0]: %s", a0);
          BTORLOG (3, "      assignment e[1]: %s", a1);
          btor_freestr (btor->mm, a0);
          btor_freestr (btor->mm, a1);
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
        if (btor->options.loglevel.val >= 2)
        {
          a0 = (char *) btor_get_bv_model_str_aux (
              btor, bv_model, fun_model, cur);
          BTORLOG (3, "      assignment : %s", a0);
          btor_freestr (btor->mm, a0);
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

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  BTOR_RELEASE_STACK (btor->mm, stack);

  assert (btor_get_ptr_hash_table (score, exp));
  assert (res == btor_get_ptr_hash_table (score, exp)->data.as_dbl);
  return res;
}

static void
compute_sls_scores_aux (Btor *btor,
                        BtorPtrHashTable **bv_model,
                        BtorPtrHashTable **fun_model,
                        BtorPtrHashTable *score)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (BTOR_SLS_SOLVER (btor)->roots);
  assert (bv_model);
  assert (fun_model);
  assert (btor_check_id_table_mark_unset_dbg (btor));

  int i;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack stack, unmark_stack;
  BtorHashTableIterator it;

  BTORLOG (3, "");
  BTORLOG (3, "**** compute sls scores ***");

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  /* collect roots */
  btor_init_node_hash_table_iterator (&it, BTOR_SLS_SOLVER (btor)->roots);
  while (btor_has_next_node_hash_table_iterator (&it))
    BTOR_PUSH_STACK (btor->mm, stack, btor_next_node_hash_table_iterator (&it));

  /* compute score */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->mark == 2 || btor_get_ptr_hash_table (score, cur)) continue;

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
          && btor_get_exp_width (btor, real_cur) != 1)
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
  assert (BTOR_SLS_SOLVER (btor));
  assert (BTOR_SLS_SOLVER (btor)->roots);
  assert (score);

  int allsat;
  double res, sc, weight;
  BtorNode *root;
  BtorHashTableIterator it;

  res    = 0.0;
  allsat = 1;
  btor_init_node_hash_table_iterator (&it, BTOR_SLS_SOLVER (btor)->roots);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    weight = (double) ((BtorSLSConstrData *) it.bucket->data.as_ptr)->weight;
    root   = btor_next_node_hash_table_iterator (&it);
    sc     = btor_get_ptr_hash_table (score, root)->data.as_dbl;
    if (sc < 1.0) allsat = 0;
    res += weight * sc;
  }
  return allsat ? -1.0 : res;
}

static BtorNode *
select_candidate_constraint (Btor *btor, int nmoves)
{
  assert (btor);

  double score;
  BtorNode *res, *cur;
  BtorHashTableIterator it;
  BtorSLSSolver *slv;
  BtorPtrHashBucket *b, *sb;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv);
  assert (slv->roots);
  assert (slv->score);

  res = 0;

  if (btor->options.sls_use_bandit.val)
  {
    assert (slv->score);

    double value, max_value;
    BtorSLSConstrData *d;

    max_value = 0.0;
    btor_init_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      b   = it.bucket;
      d   = (BtorSLSConstrData *) b->data.as_ptr;
      cur = btor_next_node_hash_table_iterator (&it);
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cur))
          && btor_is_zero_bv (btor_get_bv_model (btor, cur)))
        return 0; /* contains false constraint -> unsat */
      sb = btor_get_ptr_hash_table (slv->score, cur);
      assert (sb);
      score = sb->data.as_dbl;
      if (score >= 1.0) continue;
      if (!res)
      {
        res = cur;
        d->selected += 1;
        continue;
      }

      value = score + BTOR_SLS_SELECT_CFACT * sqrt (log (d->selected) / nmoves);
      if (value > max_value)
      {
        res       = cur;
        max_value = value;
        d->selected += 1;
      }
    }
  }
  else
  {
    uint32_t r;
    BtorNodePtrStack stack;

    BTOR_INIT_STACK (stack);
    btor_init_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cur))
          && btor_is_zero_bv (btor_get_bv_model (btor, cur)))
      {
        BTOR_RELEASE_STACK (btor->mm, stack);
        return 0; /* contains false constraint -> unsat */
      }
      sb = btor_get_ptr_hash_table (slv->score, cur);
      assert (sb);
      score = sb->data.as_dbl;
      if (score >= 1.0) continue;
      BTOR_PUSH_STACK (btor->mm, stack, cur);
    }
    assert (BTOR_COUNT_STACK (stack));
    r   = btor_pick_rand_rng (&btor->rng, 0, BTOR_COUNT_STACK (stack) - 1);
    res = stack.start[r];
    BTOR_RELEASE_STACK (btor->mm, stack);
  }

  assert (res);

  BTORLOG (1, "");
  BTORLOG (1, "*** select candidate constraint: %s", node2string (res));

  return res;
}

static void
select_candidates (Btor *btor, BtorNode *root, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (btor_check_id_table_mark_unset_dbg (btor));
  assert (root);
  assert (candidates);

  int i;
  BtorNode *cur, *real_cur, *e;
  BtorNodePtrStack stack, unmark_stack, controlling;
  const BtorBitVector *bv;

  BTORLOG (1, "");
  BTORLOG (1, "*** select candidates");

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
      BTORLOG (1, "  %s", node2string (real_cur));
      continue;
    }

    /* push children */
    if (btor->options.just.val && BTOR_IS_AND_NODE (real_cur)
        && btor_get_exp_width (btor, real_cur) == 1)
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
    //      else if (btor->options.just.val && BTOR_IS_BCOND_NODE (real_cur))
    //	{
    //	  BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[0]);
    //	  bv = btor_get_bv_model (btor, real_cur->e[0]);
    //	  if (btor_is_zero_bv (bv))
    //	    BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[2]);
    //	  else
    //	    BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[1]);
    //	}
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
  cloned_data->as_ptr = btor_copy_bv (mm, (BtorBitVector *) data->as_ptr);
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
  cloned_data->as_dbl = data->as_dbl;
}

static void
reset_cone (Btor *btor,
            BtorPtrHashTable *cans,
            BtorPtrHashTable *bv_model,
            BtorPtrHashTable *score)
{
  assert (btor);
  assert (btor_check_id_table_mark_unset_dbg (btor));
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

  btor_init_node_hash_table_iterator (&it, cans);
  while (btor_has_next_node_hash_table_iterator (&it))
    BTOR_PUSH_STACK (btor->mm, stack, btor_next_node_hash_table_iterator (&it));

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->mark) continue;
    cur->mark = 1;
    BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

    /* reset previous assignment */
    if ((b = btor_get_ptr_hash_table (bv_model, cur)))
    {
      btor_free_bv (btor->mm, b->data.as_ptr);
      btor_remove_ptr_hash_table (bv_model, cur, 0, 0);
      btor_release_exp (btor, cur);
    }
    if ((b = btor_get_ptr_hash_table (bv_model, BTOR_INVERT_NODE (cur))))
    {
      btor_free_bv (btor->mm, b->data.as_ptr);
      btor_remove_ptr_hash_table (bv_model, BTOR_INVERT_NODE (cur), 0, 0);
      btor_release_exp (btor, cur);
    }
    /* reset previous score */
    if ((b = btor_get_ptr_hash_table (score, cur)))
      btor_remove_ptr_hash_table (score, cur, 0, 0);
    if ((b = btor_get_ptr_hash_table (score, BTOR_INVERT_NODE (cur))))
      btor_remove_ptr_hash_table (score, BTOR_INVERT_NODE (cur), 0, 0);

    /* push parents */
    btor_init_parent_iterator (&nit, cur);
    while (btor_has_next_parent_iterator (&nit))
      BTOR_PUSH_STACK (btor->mm, stack, btor_next_parent_iterator (&nit));
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
  assert (BTOR_SLS_SOLVER (btor));
  assert (BTOR_SLS_SOLVER (btor)->roots);
  assert (bv_model);
  assert (*bv_model);
  assert (fun_model);
  assert (*fun_model);
  assert (cans);
  assert (cans->count);
  assert (score);

  BtorHashTableIterator it;
  BtorNode *exp;
  BtorBitVector *ass;

  reset_cone (btor, cans, *bv_model, score);

  btor_init_hash_table_iterator (&it, cans);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    ass = it.bucket->data.as_ptr;
    exp = btor_next_node_hash_table_iterator (&it);
    btor_add_to_bv_model (btor, *bv_model, exp, ass);
  }

  btor_generate_model (btor, *bv_model, *fun_model, 0);
  compute_sls_scores_aux (btor, bv_model, fun_model, score);
}

static inline void
update_assertion_weights (Btor *btor)
{
  assert (btor);

  BtorNode *cur;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);

  if (!btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_SCORE_F))
  {
    /* decrease the weight of all satisfied assertions */
    btor_init_node_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      b   = it.bucket;
      cur = btor_next_node_hash_table_iterator (&it);
      if (btor_get_ptr_hash_table (slv->score, cur)->data.as_dbl == 0.0)
        continue;
      if (((BtorSLSConstrData *) b->data.as_ptr)->weight > 1)
        ((BtorSLSConstrData *) b->data.as_ptr)->weight -= 1;
    }
  }
  else
  {
    /* increase the weight of all unsatisfied assertions */
    btor_init_node_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      b   = it.bucket;
      cur = btor_next_node_hash_table_iterator (&it);
      if (btor_get_ptr_hash_table (slv->score, cur)->data.as_dbl == 1.0)
        continue;
      ((BtorSLSConstrData *) b->data.as_ptr)->weight += 1;
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
  assert (BTOR_SLS_SOLVER (btor));
  assert (BTOR_SLS_SOLVER (btor)->roots);
  assert (bv_model);
  assert (score);
  assert (cans);
  assert (cans->count);

  BTOR_SLS_SOLVER (btor)->stats.flips += 1;

#ifndef NBTORLOG
  char *a;
  BtorNode *can;
  BtorBitVector *prev_ass, *new_ass;
  BtorHashTableIterator it;

  BTORLOG (2, "");
  BTORLOG (2, "  * try move:");
  btor_init_hash_table_iterator (&it, cans);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    new_ass  = it.bucket->data.as_ptr;
    can      = btor_next_node_hash_table_iterator (&it);
    prev_ass = (BtorBitVector *) btor_get_bv_model (btor, can);
    BTORLOG (2,
             "      candidate: %s%s",
             BTOR_IS_REGULAR_NODE (can) ? "" : "-",
             node2string (can));
    a = btor_bv_to_char_bv (btor->mm, prev_ass);
    BTORLOG (2, "        prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char_bv (btor->mm, new_ass);
    BTORLOG (2, "        new   assignment: %s", a);
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
            && ((sc) > slv->max_score                                          \
                || (btor->options.sls_strategy.val                             \
                        == BTOR_SLS_STRAT_BEST_SAME_MOVE                       \
                    && (sc) == slv->max_score))))                              \
    {                                                                          \
      slv->max_score = (sc);                                                   \
      slv->max_move  = mk;                                                     \
      slv->max_gw    = gw;                                                     \
      if (slv->max_cans->count)                                                \
      {                                                                        \
        btor_init_node_hash_table_iterator (&it, slv->max_cans);               \
        while (btor_has_next_node_hash_table_iterator (&it))                   \
        {                                                                      \
          assert (it.bucket->data.as_ptr);                                     \
          btor_free_bv (                                                       \
              btor->mm,                                                        \
              btor_next_data_node_hash_table_iterator (&it)->as_ptr);          \
        }                                                                      \
      }                                                                        \
      btor_delete_ptr_hash_table (slv->max_cans);                              \
      slv->max_cans = cans;                                                    \
      if (done                                                                 \
          || btor->options.sls_strategy.val == BTOR_SLS_STRAT_FIRST_BEST_MOVE) \
        goto DONE;                                                             \
    }                                                                          \
    else if (btor->options.sls_strategy.val == BTOR_SLS_STRAT_PROB_RAND_WALK)  \
    {                                                                          \
      BTOR_NEW (btor->mm, m);                                                  \
      m->cans = cans;                                                          \
      m->sc   = (sc);                                                          \
      BTOR_PUSH_STACK (btor->mm, slv->moves, m);                               \
      slv->sum_score += m->sc;                                                 \
    }                                                                          \
    else                                                                       \
    {                                                                          \
      btor_init_node_hash_table_iterator (&it, cans);                          \
      while (btor_has_next_node_hash_table_iterator (&it))                     \
        btor_free_bv (btor->mm,                                                \
                      btor_next_data_hash_table_iterator (&it)->as_ptr);       \
      btor_delete_ptr_hash_table (cans);                                       \
    }                                                                          \
  } while (0)

static inline int
select_inc_dec_not_move (Btor *btor,
                         BtorBitVector *(*fun) (BtorMemMgr *, BtorBitVector *),
                         BtorNodePtrStack *candidates,
                         int gw)
{
  double sc;
  int i, done = 0;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);

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
      btor->mm, slv->score, same_node, data_as_double, 0, 0);

  cans = btor_new_ptr_hash_table (btor->mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);

  for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
  {
    can = BTOR_PEEK_STACK (*candidates, i);
    assert (can);

    ass = (BtorBitVector *) btor_get_bv_model (btor, can);
    assert (ass);

    b         = btor_get_ptr_hash_table (slv->max_cans, can);
    max_neigh = b ? b->data.as_ptr : 0;

    b              = btor_add_ptr_hash_table (cans, can);
    b->data.as_ptr = btor->options.sls_move_inc_move_test.val && max_neigh
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
  int i, n_endpos, done = 0;
  uint32_t pos, cpos;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);

  mk = BTOR_SLS_MOVE_FLIP;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, data_as_double, 0, 0);

  for (pos = 0, n_endpos = 0; n_endpos < BTOR_COUNT_STACK (*candidates); pos++)
  {
    cans = btor_new_ptr_hash_table (btor->mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

    for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
    {
      can = BTOR_PEEK_STACK (*candidates, i);
      assert (can);

      ass = (BtorBitVector *) btor_get_bv_model (btor, can);
      assert (ass);

      b         = btor_get_ptr_hash_table (slv->max_cans, can);
      max_neigh = b ? b->data.as_ptr : 0;

      if (pos == ass->width - 1) n_endpos += 1;
      cpos = pos % ass->width;

      b              = btor_add_ptr_hash_table (cans, can);
      b->data.as_ptr = btor->options.sls_move_inc_move_test.val && max_neigh
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
  int i, n_endpos, done = 0;
  uint32_t up, cup, clo;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);

  mk = BTOR_SLS_MOVE_FLIP_RANGE;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, data_as_double, 0, 0);

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

      ass = (BtorBitVector *) btor_get_bv_model (btor, can);
      assert (ass);

      b         = btor_get_ptr_hash_table (slv->max_cans, can);
      max_neigh = b ? b->data.as_ptr : 0;

      clo = 0;
      cup = up;
      if (up >= ass->width)
      {
        if ((up - 1) / 2 < ass->width) n_endpos += 1;
        cup = ass->width - 1;
      }

      b = btor_add_ptr_hash_table (cans, can);

      /* range from MSB rather than LSB with given prob */
      if (btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_RANGE_MSB_VS_LSB))
      {
        clo = ass->width - 1 - cup;
        cup = ass->width - 1;
      }

      b->data.as_ptr =
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
  int i, ctmp, n_endpos, done = 0;
  uint32_t lo, clo, up, cup, seg;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);

  mk = BTOR_SLS_MOVE_FLIP_SEGMENT;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, data_as_double, 0, 0);

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

        ass = (BtorBitVector *) btor_get_bv_model (btor, can);
        assert (ass);

        b         = btor_get_ptr_hash_table (slv->max_cans, can);
        max_neigh = b ? b->data.as_ptr : 0;

        clo = lo;
        cup = up;

        if (up >= ass->width)
        {
          if (up - seg < ass->width) n_endpos += 1;
          cup = ass->width - 1;
        }

        if (lo >= ass->width - 1) clo = ass->width < seg ? 0 : ass->width - seg;

        b = btor_add_ptr_hash_table (cans, can);

        /* range from MSB rather than LSB with given prob */
        if (btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_SEG_MSB_VS_LSB))
        {
          ctmp = clo;
          clo  = ass->width - 1 - cup;
          cup  = ass->width - 1 - ctmp;
        }

        b->data.as_ptr =
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
  int i, n_endpos, done = 0;
  uint32_t up, cup, clo;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);

  mk = BTOR_SLS_MOVE_RAND;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, data_as_double, 0, 0);

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

      ass = (BtorBitVector *) btor_get_bv_model (btor, can);
      assert (ass);

      clo = 0;
      cup = up;
      if (up >= ass->width)
      {
        if ((up - 1) / 2 < ass->width) n_endpos += 1;
        cup = ass->width - 1;
      }

      /* range from MSB rather than LSB with given prob */
      if (btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_RANGE_MSB_VS_LSB))
      {
        clo = ass->width - 1 - cup;
        cup = ass->width - 1;
      }
      btor_add_ptr_hash_table (cans, can)->data.as_ptr =
          btor_new_random_bit_range_bv (
              btor->mm, &btor->rng, ass->width, cup, clo);
    }

    sc = try_move (btor, &bv_model, score, cans);
    if (rand_max_score == -1.0 || sc > rand_max_score)
    {
      /* reset, use current */
      slv->max_score = -1.0;
      rand_max_score = sc;
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
  assert (candidates);

  int i, r, done, randomizeall;
  double rd, sum;
  BtorNode *can;
  BtorBitVector *neigh;
  BtorNodePtrStack cans;
  BtorSLSMove *m;
  BtorHashTableIterator it;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv->max_cans);
  assert (!slv->max_cans->count);

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
    assert (slv->max_cans->count == 0);
    assert (BTOR_COUNT_STACK (slv->moves));

    qsort (slv->moves.start,
           BTOR_COUNT_STACK (slv->moves),
           sizeof (BtorSLSMove *),
           cmp_sls_moves_qsort);

    rd  = btor_pick_rand_dbl_rng (&btor->rng, 0, slv->sum_score);
    m   = BTOR_PEEK_STACK (slv->moves, 0);
    sum = m->sc;
    //      printf ("sumscore: %f r: %f sum: %f\n",
    //	      slv->sum_score, rd, sum);
    for (i = 0; i < BTOR_COUNT_STACK (slv->moves); i++)
    {
      sum += BTOR_PEEK_STACK (slv->moves, i)->sc;
      if (sum > rd) break;
      m = BTOR_PEEK_STACK (slv->moves, i);
    }
    //      printf ("sum: %f\n", sum);

    slv->max_gw   = m->cans->count > 1;
    slv->max_move = BTOR_SLS_MOVE_RAND_WALK;
    btor_init_node_hash_table_iterator (&it, m->cans);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      neigh = btor_copy_bv (btor->mm, it.bucket->data.as_ptr);
      assert (neigh);
      can = btor_next_node_hash_table_iterator (&it);
      btor_add_ptr_hash_table (slv->max_cans, can)->data.as_ptr = neigh;
    }
  }

  if (slv->max_cans->count == 0)
  {
    assert (slv->max_move == BTOR_SLS_MOVE_DONE);

    /* randomize if no best move was found */
    randomizeall =
        btor->options.sls_move_rand_all.val
            ? btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_RAND_ALL_VS_ONE)
            : 0;

    if (randomizeall)
    {
      slv->max_gw   = 1;
      slv->max_move = BTOR_SLS_MOVE_RAND;

      for (r = 0; r <= BTOR_COUNT_STACK (*candidates) - 1; r++)
      {
        can = BTOR_PEEK_STACK (*candidates, r);
        if (btor_get_exp_width (btor, can) == 1)
          neigh = btor_flipped_bit_bv (
              btor->mm, (BtorBitVector *) btor_get_bv_model (btor, can), 0);
        else
          neigh = btor_new_random_bv (
              btor->mm, &btor->rng, btor_get_exp_width (btor, can));

        btor_add_ptr_hash_table (slv->max_cans, can)->data.as_ptr = neigh;
      }
    }
    else
    {
      slv->max_gw   = 0;
      slv->max_move = BTOR_SLS_MOVE_RAND;

      can = BTOR_PEEK_STACK (
          *candidates,
          btor_pick_rand_rng (
              &btor->rng, 0, BTOR_COUNT_STACK (*candidates) - 1));

      if (btor_get_exp_width (btor, can) == 1)
      {
        neigh = btor_flipped_bit_bv (
            btor->mm, (BtorBitVector *) btor_get_bv_model (btor, can), 0);
        btor_add_ptr_hash_table (slv->max_cans, can)->data.as_ptr = neigh;
      }
      /* pick neighbor with randomized bit range (best guess) */
      else if (btor->options.sls_move_rand_range.val)
      {
        assert (!BTOR_COUNT_STACK (cans));
        BTOR_PUSH_STACK (btor->mm, cans, can);
        select_rand_range_move (btor, &cans, 0);
        BTOR_RESET_STACK (cans);
        assert (slv->max_cans->count == 1);
        assert (slv->max_cans->first->key == can);
      }
      else
      {
        neigh = btor_new_random_bv (
            btor->mm, &btor->rng, btor_get_exp_width (btor, can));
        btor_add_ptr_hash_table (slv->max_cans, can)->data.as_ptr = neigh;
      }

      assert (!slv->max_gw);
      assert (slv->max_move == BTOR_SLS_MOVE_RAND);
    }
    assert (slv->max_cans->count);
  }

DONE:
  BTOR_RELEASE_STACK (btor->mm, cans);
  while (!BTOR_EMPTY_STACK (slv->moves))
  {
    m = BTOR_POP_STACK (slv->moves);
    btor_init_node_hash_table_iterator (&it, m->cans);
    while (btor_has_next_node_hash_table_iterator (&it))
      btor_free_bv (btor->mm, btor_next_data_hash_table_iterator (&it)->as_ptr);
    btor_delete_ptr_hash_table (m->cans);
    BTOR_DELETE (btor->mm, m);
  }
}

static inline void
select_random_move (Btor *btor, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (candidates);

  int i;
  uint32_t r, up, lo;
  BtorSLSMoveKind mk;
  BtorNodePtrStack cans, *pcans;
  BtorNode *can;
  BtorBitVector *ass, *neigh;
  BtorPtrHashTable *max_cans;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv->max_cans);
  assert (!slv->max_cans->count);

  BTOR_INIT_STACK (cans);

  max_cans      = slv->max_cans;
  slv->max_move = BTOR_SLS_MOVE_RAND_WALK;

  /* select candidate(s) */
  if (btor->options.sls_move_gw.val
      && !btor_pick_rand_rng (&btor->rng, 0, BTOR_SLS_PROB_SINGLE_VS_GW))
  {
    pcans       = candidates;
    slv->max_gw = 1;
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
    pcans       = &cans;
    slv->max_gw = 0;
  }

  /* select neighbor(s) */
  for (i = 0; i < BTOR_COUNT_STACK (*pcans); i++)
  {
    can = BTOR_PEEK_STACK ((*pcans), i);
    ass = (BtorBitVector *) btor_get_bv_model (btor, can);
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

    btor_add_ptr_hash_table (max_cans, can)->data.as_ptr = neigh;
  }

  BTOR_RELEASE_STACK (btor->mm, cans);
}

/*------------------------------------------------------------------------*/

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_add_bv (Btor *btor,
            BtorNode *add,
            BtorBitVector *bvadd,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (add);
  assert (BTOR_IS_REGULAR_NODE (add));
  assert (bvadd);
  assert (bve);
  assert (bve->width == bvadd->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (add->e[eidx])));

  BtorBitVector *res;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
#endif

  mm = btor->mm;
  (void) add;
  (void) eidx;

  /* res + bve = bve + res = bvadd -> res = bvadd - bve */
  res = btor_sub_bv (mm, bvadd, bve);
#ifndef NDEBUG
  if (eidx)
    tmpdbg = btor_add_bv (mm, bve, res);
  else
    tmpdbg = btor_add_bv (mm, res, bve);
  assert (!btor_compare_bv (tmpdbg, bvadd));
  btor_free_bv (mm, tmpdbg);
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_and_bv (Btor *btor,
            BtorNode *and,
            BtorBitVector *bvand,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (and);
  assert (BTOR_IS_REGULAR_NODE (and));
  assert (bvand);
  assert (bve);
  assert (bve->width == bvand->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (and->e[eidx])));

  uint32_t i;
  int bitand, bite, isreccon;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = and->e[eidx ? 0 : 1];
  assert (e);

  res = btor_new_bv (mm, bvand->width);

  for (i = 0, isreccon = 0; i < bvand->width; i++)
  {
    bitand = btor_get_bit_bv (bvand, i);
    bite   = btor_get_bit_bv (bve, i);
    /* all bits set in bvand, must be set in bve, else conflict */
    if (bitand&&!bite)
    {
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        btor_free_bv (mm, res);
        res = 0;
        break;
      }

      isreccon = 1;
    }
    /* res & bve = bve & res = bvand
     * -> all bits set in bvand and bve must be set in res
     * -> all bits not set in bvand but set in bve must not be set in res
     * -> all bits not set in bve can be chosen to be set randomly */
    if (bitand)
      btor_set_bit_bv (res, i, 1);
    else if (bite)
      btor_set_bit_bv (res, i, 0);
    else
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }

  BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += isreccon;

#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
      tmpdbg = btor_and_bv (mm, bve, res);
    else
      tmpdbg = btor_and_bv (mm, res, bve);
    assert (!btor_compare_bv (tmpdbg, bvand));
    btor_free_bv (mm, tmpdbg);
  }
  else
  {
    for (i = 0; res && i < bvand->width; i++)
      assert (!btor_get_bit_bv (bvand, i) || btor_get_bit_bv (res, i));
  }
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_eq_bv (
    Btor *btor, BtorNode *eq, BtorBitVector *bveq, BtorBitVector *bve, int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (eq);
  assert (BTOR_IS_REGULAR_NODE (eq));
  assert (bveq);
  assert (bveq->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (eq->e[eidx])));

  BtorBitVector *res;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
#endif

  mm = btor->mm;
  (void) eq;
  (void) eidx;

  /* res != bveq -> choose random res != bveq */
  if (btor_is_zero_bv (bveq))
  {
    res = 0;
    do
    {
      if (res) btor_free_bv (mm, res);
      res = btor_new_random_bv (mm, &btor->rng, bve->width);
    } while (!btor_compare_bv (res, bve));
  }
  /* res = bveq */
  else
    res = btor_copy_bv (mm, bve);

#ifndef NDEBUG
  if (eidx)
    tmpdbg = btor_eq_bv (mm, bve, res);
  else
    tmpdbg = btor_eq_bv (mm, res, bve);
  assert (!btor_compare_bv (tmpdbg, bveq));
  btor_free_bv (mm, tmpdbg);
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_ult_bv (Btor *btor,
            BtorNode *ult,
            BtorBitVector *bvult,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (ult);
  assert (BTOR_IS_REGULAR_NODE (ult));
  assert (bvult);
  assert (bvult->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (ult->e[eidx])));

  int isult, bw;
  BtorNode *e;
  BtorBitVector *res, *zero, *one, *bvmax, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = ult->e[eidx ? 0 : 1];
  assert (e);

  zero  = btor_new_bv (mm, bve->width);
  one   = btor_one_bv (mm, bve->width);
  bvmax = btor_ones_bv (mm, bve->width);
  isult = !btor_is_zero_bv (bvult);
  bw    = bve->width;

  if (eidx)
  {
    /* conflict: 1...1 < e[1] */
    if (!btor_compare_bv (bve, bvmax) && isult)
    {
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
      }
      else if (isult)
      {
        res = btor_new_random_range_bv (mm, &btor->rng, bw, one, bvmax);
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
      }
      else
      {
        tmp = btor_sub_bv (mm, bvmax, one);
        res = btor_new_random_range_bv (mm, &btor->rng, bw, zero, tmp);
        btor_free_bv (mm, tmp);
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
      }
    }
    else
    {
      /* bve >= e[1] */
      if (!isult)
        res = btor_new_random_range_bv (mm, &btor->rng, bw, zero, bve);
      /* bve < e[1] */
      else
      {
        tmp = btor_add_bv (mm, bve, one);
        res = btor_new_random_range_bv (mm, &btor->rng, bw, tmp, bvmax);
        btor_free_bv (mm, tmp);
      }
    }
  }
  else
  {
    /* conflict: e[0] < 0 */
    if (btor_is_zero_bv (bve) && isult)
    {
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
      }
      else if (!isult)
      {
        res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, one, bvmax);
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
      }
      else
      {
        tmp = btor_sub_bv (btor->mm, bvmax, one);
        res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, zero, tmp);
        btor_free_bv (btor->mm, tmp);
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
      }
    }
    else
    {
      /* e[0] >= bve */
      if (!isult)
        res = btor_new_random_range_bv (mm, &btor->rng, bw, bve, bvmax);
      /* e[0] < bve */
      else
      {
        tmp = btor_sub_bv (mm, bve, one);
        res = btor_new_random_range_bv (mm, &btor->rng, bw, zero, tmp);
        btor_free_bv (mm, tmp);
      }
    }
  }

#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
      tmpdbg = btor_ult_bv (mm, bve, res);
    else
      tmpdbg = btor_ult_bv (mm, res, bve);
    assert (!btor_compare_bv (tmpdbg, bvult));
    btor_free_bv (mm, tmpdbg);
  }
#endif
  btor_free_bv (mm, zero);
  btor_free_bv (mm, one);
  btor_free_bv (mm, bvmax);
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_sll_bv (Btor *btor,
            BtorNode *sll,
            BtorBitVector *bvsll,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (sll);
  assert (BTOR_IS_REGULAR_NODE (sll));
  assert (bvsll);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsll->width);
  assert (eidx || btor_log_2_util (bvsll->width) == bve->width);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (sll->e[eidx])));

  uint32_t i, j, shift;
  int oneidx;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = sll->e[eidx ? 0 : 1];
  assert (e);

  /* bve << e[1] = bvsll
   * -> identify possible shift value via zero LSB in bvsll
   *    (considering zero LSB in bve) */
  if (eidx)
  {
    for (i = 0, oneidx = -1; i < bvsll->width; i++)
    {
      if (btor_get_bit_bv (bvsll, i)) break;
      if (oneidx == -1 && btor_get_bit_bv (bve, i)) oneidx = i;
    }
    shift = oneidx == -1 ? 0 : i - oneidx;
#ifndef NDEBUG
    for (i = 0; i < shift; i++) assert (!btor_get_bit_bv (bvsll, i));
#endif

    /* check for conflict -> do not allow shift by bw */
    if (shift > bvsll->width - 1)
    {
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e))) return 0;
#ifndef NDEBUG
      iscon = 1;
#endif
      BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
    }

    /* check for conflict -> shifted bits must match */
    for (i = 0, j = shift; i < bve->width - j; i++)
    {
      if (btor_get_bit_bv (bve, i) != btor_get_bit_bv (bvsll, j + i))
      {
        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e))) return 0;
#ifndef NDEBUG
        iscon = 1;
#endif
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        break;
      }
    }

    res = btor_uint64_to_bv (
        mm, (uint64_t) shift, btor_log_2_util (bvsll->width));
  }
  /* e[0] << bve = bvsll
   * -> e[0] = bvsll >> bve
   *    set irrelevant MSBs (the ones that get shifted out) randomly */
  else
  {
    /* cast is no problem (max bit width handled by Boolector is INT_MAX) */
    shift = (int) btor_bv_to_uint64_bv (bve);

    /* check for conflict -> the LSBs shifted must be zero */
    for (i = 0; i < shift; i++)
    {
      if (btor_get_bit_bv (bvsll, i))
      {
        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e))) return 0;
#ifndef NDEBUG
        iscon = 1;
#endif
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        break;
      }
    }

    res = btor_srl_bv (mm, bvsll, bve);
    for (i = 0; i < shift; i++)
      btor_set_bit_bv (
          res, res->width - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }
#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
      tmpdbg = btor_sll_bv (mm, bve, res);
    else
      tmpdbg = btor_sll_bv (mm, res, bve);
    assert (!btor_compare_bv (tmpdbg, bvsll));
    btor_free_bv (mm, tmpdbg);
  }
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_srl_bv (Btor *btor,
            BtorNode *srl,
            BtorBitVector *bvsrl,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (srl);
  assert (BTOR_IS_REGULAR_NODE (srl));
  assert (bvsrl);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsrl->width);
  assert (eidx || btor_log_2_util (bvsrl->width) == bve->width);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (srl->e[eidx])));

  uint32_t i, j, shift;
  int oneidx;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = srl->e[eidx ? 0 : 1];
  assert (e);

  /* bve >> e[1] = bvsll
   * -> identify possible shift value via zero MSBs in bvsll
   *    (considering zero MSBs in bve) */
  if (eidx)
  {
    for (i = 0, oneidx = -1; i < bvsrl->width; i++)
    {
      if (btor_get_bit_bv (bvsrl, bvsrl->width - 1 - i)) break;
      if (oneidx == -1 && btor_get_bit_bv (bve, bve->width - 1 - i)) oneidx = i;
    }
    shift = oneidx == -1 ? 0 : i - oneidx;
#ifndef NDEBUG
    for (i = 0; i < shift; i++)
      assert (!btor_get_bit_bv (bvsrl, bvsrl->width - 1 - i));
#endif
    /* check for conflict -> do not allow shift by bw */
    if (shift > bvsrl->width - 1)
    {
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e))) return 0;
#ifndef NDEBUG
      iscon = 1;
#endif
      BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
    }

    /* check for conflict -> shifted bits must match */
    for (i = 0, j = shift; i < bve->width - j; i++)
    {
      if (btor_get_bit_bv (bve, bve->width - 1 - i)
          != btor_get_bit_bv (bvsrl, bvsrl->width - 1 - (j + i)))
      {
        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e))) return 0;
#ifndef NDEBUG
        iscon = 1;
#endif
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        break;
      }
    }

    res = btor_uint64_to_bv (
        mm, (uint64_t) shift, btor_log_2_util (bvsrl->width));
  }
  /* e[0] >> bve = bvsll
   * -> e[0] = bvsll << bve
   *    set irrelevant LSBs (the ones that get shifted out) randomly */
  else
  {
    /* cast is no problem (max bit width handled by Boolector is INT_MAX) */
    shift = (int) btor_bv_to_uint64_bv (bve);

    /* check for conflict -> the MSBs shifted must be zero */
    for (i = 0; i < shift; i++)
    {
      if (btor_get_bit_bv (bvsrl, bvsrl->width - 1 - i))
      {
        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e))) return 0;
#ifndef NDEBUG
        iscon = 1;
#endif
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        break;
      }
    }

    res = btor_sll_bv (mm, bvsrl, bve);
    for (i = 0; i < shift; i++)
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }

#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
      tmpdbg = btor_srl_bv (mm, bve, res);
    else
      tmpdbg = btor_srl_bv (mm, res, bve);
    assert (!btor_compare_bv (tmpdbg, bvsrl));
    btor_free_bv (mm, tmpdbg);
  }
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_mul_bv (Btor *btor,
            BtorNode *mul,
            BtorBitVector *bvmul,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (mul);
  assert (BTOR_IS_REGULAR_NODE (mul));
  assert (bvmul);
  assert (bve);
  assert (bve->width == bvmul->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (mul->e[eidx])));

  BtorNode *e;
  BtorBitVector *res, *inv, *tmp, *tmp2;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = mul->e[eidx ? 0 : 1];
  assert (e);

  /* res * bve = bve * res = bvmul
   * -> if bve is a divisor of bvmul, res = bvmul / bve
   * -> if bve odd (gcd (bve, 2^bw) == 1), determine res via extended euclid
   * -> else conflict */

  tmp = btor_urem_bv (mm, bvmul, bve);
  if (btor_is_zero_bv (tmp))
  {
    btor_free_bv (mm, tmp);
    res = btor_udiv_bv (mm, bvmul, bve);
  }
  else
  {
    btor_free_bv (mm, tmp);

    if (btor_get_bit_bv (bve, 0)) /* odd */
    {
      inv = btor_mod_inverse_bv (mm, bve);
      res = btor_mul_bv (mm, inv, bvmul);
      btor_free_bv (mm, inv);
    }
    else /* conflict */
    {
      int i;
      uint64_t div[4] = {7, 5, 3, 2};

      // TODO if bvmul even, choose m*2 as divisor (1 randomly shifted to left)
      // TODO else choose random odd number with rem 0
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
      }
      else
      {
        res = 0;
        if (bvmul->width > 2)
        {
          for (i = bvmul->width < 3 ? 2 : 0; i < 4; i++)
          {
            tmp2 = btor_uint64_to_bv (mm, div[i], bvmul->width);
            if (btor_compare_bv (bvmul, tmp2) > 0)
            {
              tmp = btor_urem_bv (mm, bvmul, tmp2);
              if (btor_is_zero_bv (tmp))
              {
                res = btor_udiv_bv (mm, bvmul, tmp2);
                btor_free_bv (mm, tmp2);
                btor_free_bv (mm, tmp);
                break;
              }
              btor_free_bv (mm, tmp);
            }
            btor_free_bv (mm, tmp2);
          }
        }

        if (!res) res = btor_uint64_to_bv (mm, 1, bvmul->width);

        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
      }
    }
  }
#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
      tmpdbg = btor_mul_bv (mm, bve, res);
    else
      tmpdbg = btor_mul_bv (mm, res, bve);
    assert (!btor_compare_bv (tmpdbg, bvmul));
    btor_free_bv (mm, tmpdbg);
  }
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_udiv_bv (Btor *btor,
             BtorNode *udiv,
             BtorBitVector *bvudiv,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);
  assert (bve->width == bvudiv->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (udiv->e[eidx])));

  BtorNode *e;
  BtorBitVector *res, *tmp, *one, *bvmax, *n;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = udiv->e[eidx ? 0 : 1];
  assert (e);

  one   = btor_one_bv (mm, bve->width);
  bvmax = btor_ones_bv (mm, bvudiv->width); /* 2^bw - 1 */

  /* bve / e[1] = bvudiv
   * -> if bvudiv is a divisor of bve, res = bve * bvudiv
   * -> else conflict */
  if (eidx)
  {
    if (btor_is_zero_bv (bve))
    {
      /* 0 / e[1] = 0, else conflict */
      if (btor_is_zero_bv (bvudiv))
        res = btor_new_random_bv (mm, &btor->rng, bve->width);
      else
      {
#ifndef NDEBUG
        iscon = 1;
#endif
        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = 0;
        }
        else
        {
          /* e[0] = res * bvudiv s.t. res * bvudiv does not overflow */
          res =
              btor_new_random_range_bv (mm, &btor->rng, bve->width, one, bvmax);
          while (btor_is_umulo_bv (mm, res, bvudiv))
          {
            tmp = btor_sub_bv (mm, res, one);
            btor_free_bv (mm, res);
            res =
                btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);
            btor_free_bv (mm, tmp);
          }

          BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        }
      }
    }
    else
    {
      tmp = btor_urem_bv (mm, bve, bvudiv);
      if (btor_is_zero_bv (tmp))
      {
        btor_free_bv (mm, tmp);
        res = btor_udiv_bv (mm, bve, bvudiv);
      }
      else
      {
        /* conflict */
#ifndef NDEBUG
        iscon = 1;
#endif
        btor_free_bv (mm, tmp);

        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
          res = 0;
        else
        {
          tmp = btor_copy_bv (mm, bvmax);
          res = btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);

          while (btor_is_umulo_bv (mm, res, bvudiv))
          {
            btor_free_bv (mm, tmp);
            tmp = btor_sub_bv (mm, res, one);
            btor_free_bv (mm, res);
            res =
                btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);
          }

          btor_free_bv (mm, tmp);

          BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        }
      }
    }
  }
  /* e[0] / bve = bvudiv
   * -> if bvudiv * bve does not overflow, res  = bvudiv * bve
   * -> else conflict */
  else
  {
    if (btor_is_zero_bv (bve))
    {
      /* e[0] / 0 = 1...1, else conflict */
      if (!btor_compare_bv (bvmax, bvudiv))
        res = btor_new_random_bv (mm, &btor->rng, bve->width);
      else
      {
#ifndef NDEBUG
        iscon = 1;
#endif
        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
          res = 0;
        else
        {
          /* res = n * bvudiv s.t. n * bvudiv does not overflow */
          n = btor_new_random_range_bv (mm, &btor->rng, bve->width, one, bvmax);
          while (btor_is_umulo_bv (mm, n, bvudiv))
          {
            tmp = btor_sub_bv (mm, n, one);
            btor_free_bv (mm, n);
            n = btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);
            btor_free_bv (mm, tmp);
          }
          res = btor_mul_bv (mm, n, bvudiv);
          btor_free_bv (mm, n);

          BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        }
      }
    }
    else
    {
      /* check for conflict (overflow) */
      if (btor_is_umulo_bv (mm, bve, bvudiv))
      {
#ifndef NDEBUG
        iscon = 1;
#endif
        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
          res = 0;
        else
        {
          tmp = btor_sub_bv (mm, bve, one);
          res = btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);

          while (btor_is_umulo_bv (mm, res, bvudiv))
          {
            btor_free_bv (mm, tmp);
            tmp = btor_sub_bv (mm, res, one);
            btor_free_bv (mm, res);
            res =
                btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);
          }

          btor_free_bv (mm, tmp);

          tmp = res;
          res = btor_mul_bv (mm, tmp, bvudiv);
          btor_free_bv (mm, tmp);

          BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        }
      }
      /* res = bve * bvudiv */
      else
        res = btor_mul_bv (mm, bve, bvudiv);
    }
  }
  btor_free_bv (mm, bvmax);
  btor_free_bv (mm, one);
#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
    {
      tmpdbg = btor_udiv_bv (mm, bve, res);
      assert (!btor_compare_bv (tmpdbg, bvudiv));
      btor_free_bv (mm, tmpdbg);
    }
    else
    {
      tmpdbg = btor_udiv_bv (mm, res, bve);
      assert (!btor_compare_bv (tmpdbg, bvudiv));
      btor_free_bv (mm, tmpdbg);
    }
  }
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_urem_bv (Btor *btor,
             BtorNode *urem,
             BtorBitVector *bvurem,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (urem);
  assert (BTOR_IS_REGULAR_NODE (urem));
  assert (bvurem);
  assert (bve);
  assert (bve->width == bvurem->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (urem->e[eidx])));

  int cmp;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp, *tmp2, *one, *n, *mul;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = urem->e[eidx ? 0 : 1];
  assert (e);

  bvmax = btor_ones_bv (mm, bvurem->width); /* 2^bw - 1 */
  one   = btor_one_bv (mm, bvurem->width);

  /* bve % e[1] = bvurem
   * -> if bve = bvurem, choose some e[1] > bve randomly
   *    (if bve = 2^bw - 1, then conflict)
   * -> if bve > bvurem, e[1] = bve - bvurem > bvurem, else conflict
   * -> if bve < bvurem, conflict */
  if (eidx)
  {
    cmp = btor_compare_bv (bve, bvurem);
    /* bve == bvurem, choose random e[1] if not conflict */
    if (cmp == 0)
    {
      if (btor_compare_bv (bve, bvmax) < 0)
      {
        /* bve < res <= 2^bw - 1 */
        tmp = btor_add_bv (mm, bve, one);
        res = btor_new_random_range_bv (mm, &btor->rng, bve->width, tmp, bvmax);
        btor_free_bv (mm, tmp);
      }
      else /* non-recoverable conflict -> bvurem = 2^bw - 1 */
      {
      RES_GT_BVUREM:
        res = 0;
#ifndef NDEBUG
        iscon = 1;
#endif
      }
    }
    /* bve > bvurem, e[1] = (bve - bvurem) / n */
    else if (cmp > 0)
    {
      /* we choose simplest solution with n = 1
       * (if res > bvurem, else conflict) */
      // TODO maybe choose more random solution?
      // TODO if (bve-bvurem) even, n = m * 2, m >= 0 (shift 1 randomly to left)
      // TODO if odd, generate random odd numbers (+1 if even) until rem=0
      res = btor_sub_bv (mm, bve, bvurem);
      /* check for conflict */
      if (btor_compare_bv (res, bvurem) <= 0)
      {
#ifndef NDEBUG
        iscon = 1;
#endif
        btor_free_bv (mm, res);
        /* check for non-recoverable conflict */
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
          res = 0;
        else
        {
          BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
          goto RES_EQ_BVUREM_1;
        }
      }
    }
    /* bve < bvurem (conflict) */
    else
    {
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
      }
      /* still non-recoverable if bvurem = 2^bw - 1 */
      else if (!btor_compare_bv (bvurem, bvmax))
      {
        goto RES_GT_BVUREM;
      }
      else
      {
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
      RES_EQ_BVUREM_1:
        /* choose res s.t. e[0] = bvurem (simplest solution)
           -> bvurem < res <= 2^bw - 1 */
        tmp = btor_add_bv (mm, bve, one);
        res = btor_new_random_range_bv (mm, &btor->rng, bve->width, tmp, bvmax);
        btor_free_bv (mm, tmp);
      }
    }
  }
  /* e[0] % bve = bvurem
   * -> if bve <= bvurem, conflict
   * -> else choose either
   *      - e[0] = bvurem, or
   *      - e[0] = bve * n + b, with n s.t. (bve * n + b) does not overflow */
  else
  {
    if (btor_compare_bv (bve, bvurem) > 0)
    {
      /* choose simplest solution (0 <= res < bve -> res = bvurem)
       * with prob 0.5 */
      if (btor_pick_rand_rng (&btor->rng, 0, 1))
      {
        goto RES_EQ_BVUREM_0;
      }
      /* e[0] = bve * n + bvurem,
       * with n s.t. (bve * n + bvurem) does not overflow */
      else
      {
        tmp2 = btor_sub_bv (mm, bvmax, bve);

        /* check for conflict -> overflow for n = 1 */
        if (btor_compare_bv (tmp2, bvurem) < 0)
        {
          btor_free_bv (mm, tmp2);
#ifndef NDEBUG
          iscon = 1;
#endif
          /* check for non-recoverable conflict */
          if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
            res = 0;
          else
          {
            BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
            goto RES_EQ_BVUREM_0;
          }
        }
        else
        {
          btor_free_bv (mm, tmp2);

          tmp = btor_copy_bv (mm, bvmax);
          n   = btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);

          while (btor_is_umulo_bv (mm, bve, n))
          {
            btor_free_bv (mm, tmp);
            tmp = btor_sub_bv (mm, n, one);
            btor_free_bv (mm, n);
            n = btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);
          }

          mul  = btor_mul_bv (mm, bve, n);
          tmp2 = btor_sub_bv (mm, bvmax, mul);

          if (btor_compare_bv (tmp2, bvurem) < 0)
          {
            btor_free_bv (mm, tmp);
            tmp = btor_sub_bv (mm, n, one);
            btor_free_bv (mm, n);
            n = btor_new_random_range_bv (mm, &btor->rng, bve->width, one, tmp);
            btor_free_bv (mm, mul);
            mul = btor_mul_bv (mm, bve, n);
          }

          res = btor_add_bv (mm, mul, bvurem);
          assert (btor_compare_bv (res, mul) >= 0);
          assert (btor_compare_bv (res, bvurem) >= 0);

          btor_free_bv (mm, tmp);
          btor_free_bv (mm, tmp2);
          btor_free_bv (mm, mul);
          btor_free_bv (mm, n);
        }
      }
    }
    else /* conflict */
    {
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        res = 0;
      else
      {
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
      RES_EQ_BVUREM_0:
        /* res = bvurem (simplest solution) */
        res = btor_copy_bv (mm, bvurem);
      }
    }
  }

  btor_free_bv (mm, one);
  btor_free_bv (mm, bvmax);

#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
      tmpdbg = btor_urem_bv (mm, bve, res);
    else
      tmpdbg = btor_urem_bv (mm, res, bve);
    assert (!btor_compare_bv (tmpdbg, bvurem));
    btor_free_bv (mm, tmpdbg);
  }
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_concat_bv (Btor *btor,
               BtorNode *concat,
               BtorBitVector *bvconcat,
               BtorBitVector *bve,
               int eidx)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (concat);
  assert (BTOR_IS_REGULAR_NODE (concat));
  assert (bvconcat);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (concat->e[eidx])));

  BtorNode *e;
  BtorBitVector *res, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = concat->e[eidx ? 0 : 1];
  assert (e);

  /* bve o e[1] = bvconcat, slice e[1] out of the lower bits of bvconcat */
  if (eidx)
  {
    tmp = btor_slice_bv (
        mm, bvconcat, bvconcat->width - 1, bvconcat->width - bve->width);
    /* check for conflict */
    if (btor_compare_bv (tmp, bve))
    {
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
      }
      else
      {
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        goto SLICE_EIDX1;
      }
    }
    else
    {
    SLICE_EIDX1:
      res = btor_slice_bv (mm, bvconcat, bvconcat->width - bve->width - 1, 0);
    }
  }
  /* e[0] o bve = bvconcat, slice e[0] out of the upper bits of bvconcat */
  else
  {
    tmp = btor_slice_bv (mm, bvconcat, bve->width - 1, 0);
    /* check for conflict */
    if (btor_compare_bv (tmp, bve))
    {
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
      }
      else
      {
        BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        goto SLICE_EIDX0;
      }
    }
    else
    {
    SLICE_EIDX0:
      res = btor_slice_bv (mm, bvconcat, bvconcat->width - 1, bve->width);
    }
  }
  btor_free_bv (mm, tmp);
#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
      tmpdbg = btor_concat_bv (mm, bve, res);
    else
      tmpdbg = btor_concat_bv (mm, res, bve);
    assert (!btor_compare_bv (tmpdbg, bvconcat));
    btor_free_bv (mm, tmpdbg);
  }
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_slice_bv (Btor *btor, BtorNode *slice, BtorBitVector *bvslice)
{
  assert (btor);
  assert (BTOR_SLS_SOLVER (btor));
  assert (slice);
  assert (BTOR_IS_REGULAR_NODE (slice));
  assert (bvslice);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (slice->e[0])));

  uint32_t i, upper, lower;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
#endif

  mm = btor->mm;
  e  = slice->e[0];
  assert (e);
  upper = btor_slice_get_upper (slice);
  lower = btor_slice_get_lower (slice);

  res = btor_new_bv (mm, btor_get_exp_width (btor, e));
  for (i = 0; i < lower; i++)
    btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
  for (i = lower; i <= upper; i++)
    btor_set_bit_bv (res, i, btor_get_bit_bv (bvslice, i - lower));
  for (i = upper + 1; i < res->width; i++)
    btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));

#ifndef NDEBUG
  tmpdbg = btor_slice_bv (mm, res, upper, lower);
  assert (!btor_compare_bv (tmpdbg, bvslice));
  btor_free_bv (mm, tmpdbg);
#endif
  return res;
}

/* Select neighbor by propagating assignments from a given candidate
 * constraint (which is forced to be true) downwards. A downward path is
 * chosen via justification. If a non-recoverable conflict is encountered,
 * no move is performed. */
static inline void
select_prop_move (Btor *btor, BtorNode *root)
{
  assert (btor);
  assert (btor_check_id_table_mark_unset_dbg (btor));
  assert (root);
  assert (
      btor_bv_to_uint64_bv ((BtorBitVector *) btor_get_bv_model (btor, root))
      == 0);

  int i, eidx, idx;
  BtorPtrHashBucket *b;
  BtorNode *cur, *real_cur;
  BtorBitVector *bve[3], *bvcur, *bvenew, *tmp;
  BtorSLSSolver *slv;

  slv           = BTOR_SLS_SOLVER (btor);
  slv->max_move = BTOR_SLS_MOVE_PROP;

  cur   = root;
  bvcur = btor_one_bv (btor->mm, 1);

  if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (cur)))
  {
    b = btor_add_ptr_hash_table (slv->max_cans, BTOR_REAL_ADDR_NODE (cur));
    b->data.as_ptr = BTOR_IS_INVERTED_NODE (cur)
                         ? btor_not_bv (btor->mm, bvcur)
                         : btor_copy_bv (btor->mm, bvcur);
    goto DONE;
  }

  for (;;)
  {
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!BTOR_IS_BV_COND_NODE (real_cur));
    assert (!BTOR_IS_BV_CONST_NODE (real_cur));
    assert (!BTOR_IS_BV_VAR_NODE (real_cur));
    assert (real_cur->arity <= 2);

    if (BTOR_IS_INVERTED_NODE (cur))
    {
      tmp   = bvcur;
      bvcur = btor_not_bv (btor->mm, tmp);
      btor_free_bv (btor->mm, tmp);
    }

    /* choose path */
    for (i = 0, eidx = -1; i < real_cur->arity; i++)
    {
      bve[i] = (BtorBitVector *) btor_get_bv_model (btor, real_cur->e[i]);
      /* AND: choose 0-branch if only one is 0, else choose randomly
       * Note: if bvcur = 0, no path is 0 (as the prev assignment of
       *       bvcur was 1) */
      if (BTOR_IS_AND_NODE (real_cur) && btor_is_zero_bv (bve[i]))
        eidx = eidx == -1 ? i : -1;
    }
    if (eidx == -1)
    {
      eidx = real_cur->arity > 1
                 ? (int) btor_pick_rand_rng (&btor->rng, 0, real_cur->arity - 1)
                 : 0;
    }
    idx = eidx ? 0 : 1;

    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[eidx])))
    {
      /* non-recoverable conflict */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[idx]))
          || real_cur->arity == 1)
        break;

      eidx = idx;
      idx  = eidx ? 0 : 1;
    }

    /* determine path assignment */
    switch (real_cur->kind)
    {
      case BTOR_ADD_NODE:
        bvenew = inv_add_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_AND_NODE:
        bvenew = inv_and_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_BEQ_NODE:
        bvenew = inv_eq_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_ULT_NODE:
        bvenew = inv_ult_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_SLL_NODE:
        bvenew = inv_sll_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_SRL_NODE:
        bvenew = inv_srl_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_MUL_NODE:
        bvenew = inv_mul_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_UDIV_NODE:
        bvenew = inv_udiv_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_UREM_NODE:
        bvenew = inv_urem_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      case BTOR_CONCAT_NODE:
        bvenew = inv_concat_bv (btor, real_cur, bvcur, bve[idx], eidx);
        break;
      default:
        assert (real_cur->kind == BTOR_SLICE_NODE);
        bvenew = inv_slice_bv (btor, real_cur, bvcur);
    }

    if (!bvenew) break; /* non-recoverable conflict */

    /* found candidate and neighbor */
    if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[eidx])))
    {
      cur = real_cur->e[eidx];
    ADD_CAN_NEIGH:
      b = btor_add_ptr_hash_table (slv->max_cans, BTOR_REAL_ADDR_NODE (cur));
      b->data.as_ptr = BTOR_IS_INVERTED_NODE (cur)
                           ? btor_not_bv (btor->mm, bvenew)
                           : btor_copy_bv (btor->mm, bvenew);
      btor_free_bv (btor->mm, bvenew);
      break;
    }
    else if (BTOR_IS_BV_COND_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[eidx])))
    {
      cur      = real_cur->e[eidx];
      real_cur = BTOR_REAL_ADDR_NODE (cur);
      do
      {
#if 0
	      tmp = (BtorBitVector *)
		btor_get_bv_model (btor, real_cur->e[0]);
	      /* assume cond to be fixed, propagate bvnew to enabled path */
	      if (btor_is_zero_bv (tmp))
		cur = real_cur->e[2];
	      else
		cur = real_cur->e[1];
#else
        /* either assume that cond is fixed and propagate bvenew
         * to enabled path, or flip condition */
        tmp = (BtorBitVector *) btor_get_bv_model (btor, real_cur->e[0]);
        if (btor->options.sls_move_prop_no_flip_cond.val
            || btor_pick_rand_rng (
                   &btor->rng,
                   0,
                   btor->options.sls_move_prop_flip_cond_prob.val))
        {
          /* assume cond to be fixed */
          cur = btor_is_zero_bv (tmp) ? real_cur->e[2] : real_cur->e[1];
        }
        else
        {
          /* flip condition */
          btor_free_bv (btor->mm, bvenew);
          bvenew = btor_not_bv (btor->mm, tmp);
          cur    = real_cur->e[0];
        }
#endif
        real_cur = BTOR_REAL_ADDR_NODE (cur);
      } while (BTOR_IS_BV_COND_NODE (real_cur));

      if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (cur)))
        goto ADD_CAN_NEIGH;
      else if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cur)))
      {
        /* if input is const -> conflict */
        btor_free_bv (btor->mm, bvenew);
        break;
      }
    }
    else
      cur = real_cur->e[eidx];

    btor_free_bv (btor->mm, bvcur);
    bvcur = bvenew;
  }
DONE:
  btor_free_bv (btor->mm, bvcur);
}

/*------------------------------------------------------------------------*/

static int
move (Btor *btor, int nmoves)
{
  assert (btor);

  int nprops, nsls;
  BtorNode *constr;
  BtorNodePtrStack candidates;
  BtorHashTableIterator it;
  BtorSLSSolver *slv;

  BTORLOG (1, "");
  BTORLOG (1, "*** move");

  BTOR_INIT_STACK (candidates);

  slv = BTOR_SLS_SOLVER (btor);
  assert (!slv->max_cans);
  assert (compute_sls_score_formula (btor, slv->score) != -1.0);

  constr = select_candidate_constraint (btor, nmoves);
  /* roots contain false constraint -> unsat */
  if (!constr) return 0;

  slv->max_cans = btor_new_ptr_hash_table (btor->mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);

  nprops = btor->options.sls_move_prop_n_prop.val;
  nsls   = btor->options.sls_move_prop_n_sls.val;

  /* Always perform propagation moves first, i.e. perform moves
   * with ratio nprops:nsls of propagation to sls moves */
  if (btor->options.sls_strategy.val == BTOR_SLS_STRAT_ALWAYS_PROP
      || (btor->options.sls_move_prop.val && slv->npropmoves < nprops))
  {
    slv->npropmoves += 1;
    select_prop_move (btor, constr);
    if (!slv->max_cans->count)
    {
      slv->stats.move_prop_non_rec_conf += 1;
      /* force random walk if prop move fails */
      if (btor->options.sls_move_prop_force_rw.val)
      {
        select_candidates (btor, constr, &candidates);
        goto SLS_MOVE_RAND_WALK;
      }

      goto SLS_MOVE;
    }
  }
  else
  {
    slv->nslsmoves += 1;
  SLS_MOVE:
    select_candidates (btor, constr, &candidates);
    /* unsatisfied root constraint with no reachable variables -> unsat */
    if (!BTOR_COUNT_STACK (candidates)) return 0;

    slv->max_score = compute_sls_score_formula (btor, slv->score);
    slv->max_move  = BTOR_SLS_MOVE_DONE;
    slv->max_gw    = -1;

    if (btor->options.sls_move_rand_walk.val
        && !btor_pick_rand_rng (
               &btor->rng, 0, btor->options.sls_move_rand_walk_prob.val))
    {
    SLS_MOVE_RAND_WALK:
      select_random_move (btor, &candidates);
    }
    else
    {
      select_move (btor, &candidates);
    }

    assert (slv->max_cans->count);
  }
  assert (slv->max_move != BTOR_SLS_MOVE_DONE);

  if (nprops == slv->npropmoves && nsls == slv->nslsmoves)
  {
    slv->npropmoves = slv->nslsmoves = 0;
  }

#ifndef NBTORLOG
  BTORLOG (1, "");
  BTORLOG (1, " * move");
  char *a;
  BtorNode *can;
  BtorBitVector *neigh, *ass;
  btor_init_node_hash_table_iterator (&it, slv->max_cans);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    neigh = it.bucket->data.as_ptr;
    can   = btor_next_node_hash_table_iterator (&it);
    ass   = (BtorBitVector *) btor_get_bv_model (btor, can);
    a     = btor_bv_to_char_bv (btor->mm, ass);
    BTORLOG (1,
             "  candidate: %s%s",
             BTOR_IS_REGULAR_NODE (can) ? "" : "-",
             node2string (can));
    BTORLOG (1, "  prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char_bv (btor->mm, neigh);
    BTORLOG (1, "  new   assignment: %s", a);
    btor_freestr (btor->mm, a);
  }
#endif

  update_cone (
      btor, &btor->bv_model, &btor->fun_model, slv->max_cans, slv->score);

  slv->stats.moves += 1;

  assert (slv->max_move != BTOR_SLS_MOVE_DONE);
  assert (slv->max_gw >= 0);

  switch (slv->max_move)
  {
    case BTOR_SLS_MOVE_FLIP:
      if (!slv->max_gw)
        slv->stats.move_flip += 1;
      else
        slv->stats.move_gw_flip += 1;
      break;
    case BTOR_SLS_MOVE_INC:
      if (!slv->max_gw)
        slv->stats.move_inc += 1;
      else
        slv->stats.move_gw_inc += 1;
      break;
    case BTOR_SLS_MOVE_DEC:
      if (!slv->max_gw)
        slv->stats.move_dec += 1;
      else
        slv->stats.move_gw_dec += 1;
      break;
    case BTOR_SLS_MOVE_NOT:
      if (!slv->max_gw)
        slv->stats.move_not += 1;
      else
        slv->stats.move_gw_not += 1;
      break;
    case BTOR_SLS_MOVE_FLIP_RANGE:
      if (!slv->max_gw)
        slv->stats.move_range += 1;
      else
        slv->stats.move_gw_range += 1;
      break;
    case BTOR_SLS_MOVE_FLIP_SEGMENT:
      if (!slv->max_gw)
        slv->stats.move_seg += 1;
      else
        slv->stats.move_gw_seg += 1;
      break;
    case BTOR_SLS_MOVE_RAND:
      if (!slv->max_gw)
        slv->stats.move_rand += 1;
      else
        slv->stats.move_gw_rand += 1;
      break;
    case BTOR_SLS_MOVE_RAND_WALK:
      if (!slv->max_gw)
        slv->stats.move_rand_walk += 1;
      else
        slv->stats.move_gw_rand_walk += 1;
      break;
    default:
      assert (slv->max_move == BTOR_SLS_MOVE_PROP);
      slv->stats.move_prop += 1;
  }

  if (slv->max_move == BTOR_SLS_MOVE_RAND) update_assertion_weights (btor);

  /** cleanup **/
  btor_init_node_hash_table_iterator (&it, slv->max_cans);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_free_bv (btor->mm, btor_next_data_hash_table_iterator (&it)->as_ptr);
  btor_delete_ptr_hash_table (slv->max_cans);
  slv->max_cans = 0;
  BTOR_RELEASE_STACK (btor->mm, candidates);
  return 1;
}

/*------------------------------------------------------------------------*/

void
clone_data_as_sls_constr_data_ptr (BtorMemMgr *mm,
                                   const void *map,
                                   BtorPtrHashData *data,
                                   BtorPtrHashData *cloned_data)
{
  assert (data);
  assert (cloned_data);

  BtorSLSConstrData *d, *cd;

  (void) map;
  d = (BtorSLSConstrData *) data->as_ptr;
  BTOR_CNEW (mm, cd);
  memcpy (cd, d, sizeof (BtorSLSConstrData));
  cloned_data->as_ptr = cd;
}

static void *
clone_sls_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (btor);
  assert (exp_map);

  int i;
  BtorSLSSolver *slv;
  BtorSLSSolver *res;
  BtorSLSMove *m, *cm;

  if (!(slv = BTOR_SLS_SOLVER (btor))) return 0;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorSLSSolver));

  res->roots = btor_clone_ptr_hash_table (clone->mm,
                                          slv->roots,
                                          btor_clone_key_as_node,
                                          clone_data_as_sls_constr_data_ptr,
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

static void
delete_sls_solver (Btor *btor)
{
  assert (btor);

  BtorHashTableIterator it;
  BtorSLSMove *m;
  BtorSLSSolver *slv;

  if (!(slv = BTOR_SLS_SOLVER (btor))) return;

  if (slv->score) btor_delete_ptr_hash_table (slv->score);
  if (slv->roots) btor_delete_ptr_hash_table (slv->roots);
  while (!BTOR_EMPTY_STACK (slv->moves))
  {
    m = BTOR_POP_STACK (slv->moves);
    btor_init_node_hash_table_iterator (&it, m->cans);
    while (btor_has_next_node_hash_table_iterator (&it))
      btor_free_bv (btor->mm, btor_next_data_hash_table_iterator (&it)->as_ptr);
    btor_delete_ptr_hash_table (m->cans);
  }
  BTOR_RELEASE_STACK (btor->mm, slv->moves);
  if (slv->max_cans)
  {
    btor_init_node_hash_table_iterator (&it, slv->max_cans);
    while (btor_has_next_node_hash_table_iterator (&it))
      btor_free_bv (btor->mm, btor_next_data_hash_table_iterator (&it)->as_ptr);
    btor_delete_ptr_hash_table (slv->max_cans);
  }
  BTOR_DELETE (btor->mm, slv);
}

/* Note: failed assumptions -> no handling necessary, sls only works for SAT
 * Note: limits are currently unused */
static int
sat_sls_solver (Btor *btor, int limit0, int limit1)
{
  assert (btor);

  int j, max_steps;
  int sat_result;
  int nmoves;
  BtorNode *root;
  BtorPtrHashBucket *b;
  BtorSLSConstrData *d;
  BtorHashTableIterator it;
  BtorSLSSolver *slv;

  (void) limit0;
  (void) limit1;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv);

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

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_UNKNOWN;
    goto DONE;
  }

  sat_result = btor_simplify (btor);
  btor_update_assumptions (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->ufs->count != 0
          || (!btor->options.beta_reduce_all.val && btor->lambdas->count != 0),
      "sls engine supports QF_BV only");

  if (btor->inconsistent) goto UNSAT;

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_UNKNOWN;
    goto DONE;
  }

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  slv->api.generate_model (btor, 0, 1);

  /* collect roots */
  assert (!slv->roots);
  slv->roots = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  assert (btor->synthesized_constraints->count == 0);
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    if (!btor_get_ptr_hash_table (slv->roots, root))
    {
      b = btor_add_ptr_hash_table (slv->roots, root);
      BTOR_CNEW (btor->mm, d);
      d->weight      = 1; /* initial assertion weight */
      b->data.as_ptr = d;
    }
  }

  if (!slv->score)
    slv->score = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);

  for (;;)
  {
    if (btor_terminate_btor (btor))
    {
      sat_result = BTOR_UNKNOWN;
      goto DONE;
    }

    /* compute initial sls score */
    compute_sls_scores (btor, slv->score);

    if (compute_sls_score_formula (btor, slv->score) == -1.0)
    {
      sat_result = BTOR_SAT;
      goto SAT;
    }

    for (j = 0, max_steps = BTOR_SLS_MAXSTEPS (slv->stats.restarts + 1);
         !btor->options.sls_use_restarts.val || j < max_steps;
         j++)
    {
      if (btor_terminate_btor (btor))
      {
        sat_result = BTOR_UNKNOWN;
        goto DONE;
      }

      if (!move (btor, nmoves)) goto UNSAT;
      nmoves += 1;

      if (compute_sls_score_formula (btor, slv->score) == -1.0)
      {
        sat_result = BTOR_SAT;
        goto SAT;
      }
    }

    /* restart */
    slv->api.generate_model (btor, 0, 1);
    btor_delete_ptr_hash_table (slv->score);
    slv->score = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
    slv->stats.restarts += 1;
  }

SAT:
  assert (sat_result == BTOR_SAT);
  goto DONE;

UNSAT:
  sat_result = BTOR_UNSAT;

DONE:
  btor->valid_assignments = 1;
  if (slv->roots)
  {
    btor_init_node_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_node_hash_table_iterator (&it))
      BTOR_DELETE (
          btor->mm,
          (BtorSLSConstrData *) btor_next_data_node_hash_table_iterator (&it)
              ->as_ptr);
    btor_delete_ptr_hash_table (slv->roots);
    slv->roots = 0;
  }
  if (slv->score)
  {
    btor_delete_ptr_hash_table (slv->score);
    slv->score = 0;
  }
  btor->last_sat_result = sat_result;
  return sat_result;
}

static void
generate_model_sls_solver (Btor *btor, int model_for_all_nodes, int reset)
{
  assert (btor);

  if (!reset && btor->bv_model) return;
  btor_init_bv_model (btor, &btor->bv_model);
  btor_init_fun_model (btor, &btor->fun_model);
  btor_generate_model (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

static void
print_stats_sls_solver (Btor *btor)
{
  assert (btor);

  BtorSLSSolver *slv;

  if (!(slv = BTOR_SLS_SOLVER (btor))) return;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "sls restarts: %d", slv->stats.restarts);
  BTOR_MSG (btor->msg, 1, "sls moves: %d", slv->stats.moves);
  BTOR_MSG (btor->msg, 1, "sls flips: %d", slv->stats.flips);
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "sls propagation move conflicts (recoverable): %d",
            slv->stats.move_prop_rec_conf);
  BTOR_MSG (btor->msg,
            1,
            "sls propagation move conflicts (non-recoverable): %d",
            slv->stats.move_prop_non_rec_conf);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "sls flip        moves: %d", slv->stats.move_flip);
  BTOR_MSG (btor->msg, 1, "sls inc         moves: %d", slv->stats.move_inc);
  BTOR_MSG (btor->msg, 1, "sls dec         moves: %d", slv->stats.move_dec);
  BTOR_MSG (btor->msg, 1, "sls not         moves: %d", slv->stats.move_not);
  BTOR_MSG (btor->msg, 1, "sls range       moves: %d", slv->stats.move_range);
  BTOR_MSG (btor->msg, 1, "sls segment     moves: %d", slv->stats.move_seg);
  BTOR_MSG (btor->msg, 1, "sls random      moves: %d", slv->stats.move_rand);
  BTOR_MSG (
      btor->msg, 1, "sls random walk moves: %d", slv->stats.move_rand_walk);
  BTOR_MSG (btor->msg, 1, "sls propagation moves: %d", slv->stats.move_prop);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (
      btor->msg, 1, "sls gw flip        moves: %d", slv->stats.move_gw_flip);
  BTOR_MSG (
      btor->msg, 1, "sls gw inc         moves: %d", slv->stats.move_gw_inc);
  BTOR_MSG (
      btor->msg, 1, "sls gw dec         moves: %d", slv->stats.move_gw_dec);
  BTOR_MSG (
      btor->msg, 1, "sls gw not         moves: %d", slv->stats.move_gw_not);
  BTOR_MSG (
      btor->msg, 1, "sls gw range       moves: %d", slv->stats.move_gw_range);
  BTOR_MSG (
      btor->msg, 1, "sls gw segment     moves: %d", slv->stats.move_gw_seg);
  BTOR_MSG (
      btor->msg, 1, "sls gw random      moves: %d", slv->stats.move_gw_rand);
  BTOR_MSG (btor->msg,
            1,
            "sls gw random walk moves: %d",
            slv->stats.move_gw_rand_walk);
}

static void
print_time_stats_sls_solver (Btor *btor)
{
  (void) btor;
}

BtorSolver *
btor_new_sls_solver (Btor *btor)
{
  assert (btor);

  BtorSLSSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind = BTOR_SLS_SOLVER_KIND;

  slv->api.clone            = clone_sls_solver;
  slv->api.delet            = delete_sls_solver;
  slv->api.sat              = sat_sls_solver;
  slv->api.generate_model   = generate_model_sls_solver;
  slv->api.print_stats      = print_stats_sls_solver;
  slv->api.print_time_stats = print_time_stats_sls_solver;

  BTOR_MSG (btor->msg, 1, "enabled sls engine");

  return (BtorSolver *) slv;
}

/*------------------------------------------------------------------------*/

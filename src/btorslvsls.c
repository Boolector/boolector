/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvsls.h"

#include "btorbitvec.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btormodel.h"
#include "btorslvprop.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btornodemap.h"
#ifndef NDEBUG
#include "btorprintmodel.h"
#endif
#include "btorabort.h"
#include "btordbg.h"
#include "btorlog.h"

#include <math.h>

/* same restart scheme as in Z3 */
#define BTOR_SLS_MAXSTEPS_CFACT 100 /* same as in Z3 (c4) */
#define BTOR_SLS_MAXSTEPS(i) \
  (BTOR_SLS_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BTOR_SLS_SCORE_CFACT 0.5     /* same as in Z3 (c1) */
#define BTOR_SLS_SCORE_F_CFACT 0.025 /* same as in Z3 (c3) */
#define BTOR_SLS_SELECT_CFACT 20     /* same as in Z3 (c2) */

#define BTOR_SLS_PROB_SCORE_F 50 /* = 0.05 (same as in Z3 (sp)) */

/* choose move with one candidate rather than group-wise move
 * for random walk (prob=0.05) */
#define BTOR_SLS_PROB_SINGLE_VS_GW 50
/* randomize all candidates rather than one only (prob=0.5) */
#define BTOR_SLS_PROB_RAND_ALL_VS_ONE 500
/* start ranges from MSB rather than LSB (prob=0.5) */
#define BTOR_SLS_PROB_RANGE_MSB_VS_LSB 500
/* start segments from MSB rather than LSB (prob=0.5) */
#define BTOR_SLS_PROB_SEG_MSB_VS_LSB 500

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
  assert (exp);

  int i;
  double res, s0, s1;
  BtorNode *cur, *real_cur;
  BtorBitVector *bv0, *bv1;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack;
  BtorIntHashTable *mark;
  BtorIntHashTableData *d;
  BtorMemMgr *mm;
#ifndef NBTORLOG
  char *a0, *a1;
#endif

  res = 0.0;
  assert (BTOR_IS_BV_EQ_NODE (BTOR_REAL_ADDR_NODE (exp))
          || BTOR_IS_ULT_NODE (BTOR_REAL_ADDR_NODE (exp))
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
      else if (BTOR_IS_BV_EQ_NODE (real_cur))
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
      else if (BTOR_IS_ULT_NODE (real_cur))
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

void
btor_compute_sls_scores (Btor *btor, BtorPtrHashTable *score)
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

  if (btor_get_opt (btor, BTOR_OPT_SLS_USE_BANDIT))
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
    if (btor_get_opt (btor, BTOR_OPT_SLS_JUST) && BTOR_IS_AND_NODE (real_cur)
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
    //      else if (btor_get_opt (btor, BTOR_OPT_SLS_JUST) &&
    //      BTOR_IS_BCOND_NODE (real_cur))
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

  if (btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_SCORE_F))
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

#define BTOR_SLS_SELECT_MOVE_CHECK_SCORE(sc)                              \
  do                                                                      \
  {                                                                       \
    done = (sc) == -1.0;                                                  \
    if (done                                                              \
        || (sls_strat != BTOR_SLS_STRAT_PROB_RAND_WALK                    \
            && ((sc) > slv->max_score                                     \
                || (sls_strat == BTOR_SLS_STRAT_BEST_SAME_MOVE            \
                    && (sc) == slv->max_score))))                         \
    {                                                                     \
      slv->max_score = (sc);                                              \
      slv->max_move  = mk;                                                \
      slv->max_gw    = gw;                                                \
      if (slv->max_cans->count)                                           \
      {                                                                   \
        btor_init_node_hash_table_iterator (&it, slv->max_cans);          \
        while (btor_has_next_node_hash_table_iterator (&it))              \
        {                                                                 \
          assert (it.bucket->data.as_ptr);                                \
          btor_free_bv (                                                  \
              btor->mm,                                                   \
              btor_next_data_node_hash_table_iterator (&it)->as_ptr);     \
        }                                                                 \
      }                                                                   \
      btor_delete_ptr_hash_table (slv->max_cans);                         \
      slv->max_cans = cans;                                               \
      if (done || sls_strat == BTOR_SLS_STRAT_FIRST_BEST_MOVE) goto DONE; \
    }                                                                     \
    else if (sls_strat == BTOR_SLS_STRAT_PROB_RAND_WALK)                  \
    {                                                                     \
      BTOR_NEW (btor->mm, m);                                             \
      m->cans = cans;                                                     \
      m->sc   = (sc);                                                     \
      BTOR_PUSH_STACK (btor->mm, slv->moves, m);                          \
      slv->sum_score += m->sc;                                            \
    }                                                                     \
    else                                                                  \
    {                                                                     \
      btor_init_node_hash_table_iterator (&it, cans);                     \
      while (btor_has_next_node_hash_table_iterator (&it))                \
        btor_free_bv (btor->mm,                                           \
                      btor_next_data_hash_table_iterator (&it)->as_ptr);  \
      btor_delete_ptr_hash_table (cans);                                  \
    }                                                                     \
  } while (0)

static inline int
select_inc_dec_not_move (Btor *btor,
                         BtorBitVector *(*fun) (BtorMemMgr *, BtorBitVector *),
                         BtorNodePtrStack *candidates,
                         int gw)
{
  double sc;
  int i, done = 0;
  uint32_t sls_strat;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorSLSSolver *slv;

  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_get_opt (btor, BTOR_OPT_SLS_STRATEGY);

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
      btor->mm, btor->bv_model, copy_node, btor_clone_data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, btor_clone_data_as_dbl, 0, 0);

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

    b = btor_add_ptr_hash_table (cans, can);
    b->data.as_ptr =
        btor_get_opt (btor, BTOR_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
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
  uint32_t pos, cpos, sls_strat;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorSLSSolver *slv;

  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_get_opt (btor, BTOR_OPT_SLS_STRATEGY);

  mk = BTOR_SLS_MOVE_FLIP;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, btor_clone_data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, btor_clone_data_as_dbl, 0, 0);

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

      b = btor_add_ptr_hash_table (cans, can);
      b->data.as_ptr =
          btor_get_opt (btor, BTOR_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
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
  uint32_t up, cup, clo, sls_strat;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorSLSSolver *slv;

  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_get_opt (btor, BTOR_OPT_SLS_STRATEGY);

  mk = BTOR_SLS_MOVE_FLIP_RANGE;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, btor_clone_data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, btor_clone_data_as_dbl, 0, 0);

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
      if (btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_RANGE_MSB_VS_LSB))
      {
        clo = ass->width - 1 - cup;
        cup = ass->width - 1;
      }

      b->data.as_ptr =
          btor_get_opt (btor, BTOR_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
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
  uint32_t lo, clo, up, cup, seg, sls_strat;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorSLSSolver *slv;

  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_get_opt (btor, BTOR_OPT_SLS_STRATEGY);

  mk = BTOR_SLS_MOVE_FLIP_SEGMENT;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, btor_clone_data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, btor_clone_data_as_dbl, 0, 0);

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
        if (btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_SEG_MSB_VS_LSB))
        {
          ctmp = clo;
          clo  = ass->width - 1 - cup;
          cup  = ass->width - 1 - ctmp;
        }

        b->data.as_ptr =
            btor_get_opt (btor, BTOR_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
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
  uint32_t up, cup, clo, sls_strat;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass;
  BtorNode *can;
  BtorPtrHashTable *cans;
  BtorHashTableIterator it;
  BtorPtrHashTable *bv_model, *score;
  BtorSLSSolver *slv;

  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_get_opt (btor, BTOR_OPT_SLS_STRATEGY);

  mk = BTOR_SLS_MOVE_RAND;

  bv_model = btor_clone_ptr_hash_table (
      btor->mm, btor->bv_model, copy_node, btor_clone_data_as_bv_ptr, 0, 0);
  score = btor_clone_ptr_hash_table (
      btor->mm, slv->score, same_node, btor_clone_data_as_dbl, 0, 0);

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
      if (btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_RANGE_MSB_VS_LSB))
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
        if (!btor_get_opt (btor, BTOR_OPT_SLS_MOVE_RANGE)) continue;
        if ((done = select_flip_range_move (btor, candidates, gw))) return done;
        break;

      case BTOR_SLS_MOVE_FLIP_SEGMENT:
        if (!btor_get_opt (btor, BTOR_OPT_SLS_MOVE_SEGMENT)) continue;
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

  int i, r, done;
  bool randomizeall;
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
  if (btor_get_opt (btor, BTOR_OPT_SLS_MOVE_GW)
      && BTOR_COUNT_STACK (*candidates) > 1)
  {
    if ((done = select_move_aux (btor, candidates, 1))) goto DONE;
  }

  /* select probabilistic random walk move
   * (weighted by score; the higher the score, the higher the probability
   * that a move gets chosen) */
  if (btor_get_opt (btor, BTOR_OPT_SLS_STRATEGY)
      == BTOR_SLS_STRAT_PROB_RAND_WALK)
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
    for (i = 0; i < BTOR_COUNT_STACK (slv->moves); i++)
    {
      sum += BTOR_PEEK_STACK (slv->moves, i)->sc;
      if (sum > rd) break;
      m = BTOR_PEEK_STACK (slv->moves, i);
    }

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
    randomizeall = btor_get_opt (btor, BTOR_OPT_SLS_MOVE_RAND_ALL)
                       ? btor_pick_with_prob_rng (&btor->rng,
                                                  BTOR_SLS_PROB_RAND_ALL_VS_ONE)
                       : false;

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
      else if (btor_get_opt (btor, BTOR_OPT_SLS_MOVE_RAND_RANGE))
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
  if (btor_get_opt (btor, BTOR_OPT_SLS_MOVE_GW)
      && btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_SINGLE_VS_GW))
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

    if ((!btor_get_opt (btor, BTOR_OPT_SLS_MOVE_SEGMENT)
         && mk == BTOR_SLS_MOVE_FLIP_SEGMENT)
        || (!btor_get_opt (btor, BTOR_OPT_SLS_MOVE_RANGE)
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

static int32_t
move (Btor *btor, uint32_t nmoves)
{
  assert (btor);

  uint32_t nprops, nsls;
  int32_t res;
  BtorNode *constr, *can;
  BtorNodePtrStack candidates;
  BtorHashTableIterator it;
  BtorSLSSolver *slv;
  BtorBitVector *neigh;

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

  res = 1;

  nprops = btor_get_opt (btor, BTOR_OPT_SLS_MOVE_PROP_N_PROP);
  nsls   = btor_get_opt (btor, BTOR_OPT_SLS_MOVE_PROP_N_SLS);

  /* Always perform propagation moves first, i.e. perform moves
   * with ratio nprops:nsls of propagation to sls moves */
  if (btor_get_opt (btor, BTOR_OPT_SLS_STRATEGY) == BTOR_SLS_STRAT_ALWAYS_PROP
      || (btor_get_opt (btor, BTOR_OPT_SLS_MOVE_PROP)
          && slv->npropmoves < nprops))
  {
    slv->npropmoves += 1;
    /* Select neighbor by propagating assignments from a given candidate
     * constraint (which is forced to be true) downwards. A downward path
     * is chosen via justification. If a non-recoverable conflict is
     * encountered, no move is performed. */
    slv->max_move = BTOR_SLS_MOVE_PROP;
    btor_select_move_prop (btor, constr, &can, &neigh);
    if (can)
    {
      assert (neigh);
      btor_add_ptr_hash_table (slv->max_cans, BTOR_REAL_ADDR_NODE (can))
          ->data.as_ptr = neigh;
    }
    else /* recovery move */
    {
      slv->stats.move_prop_non_rec_conf += 1;
      /* force random walk if prop move fails */
      if (btor_get_opt (btor, BTOR_OPT_SLS_MOVE_PROP_FORCE_RW))
      {
        select_candidates (btor, constr, &candidates);
        /* root is const false -> unsat */
        if (!BTOR_COUNT_STACK (candidates))
        {
          res = 0;
          goto DONE;
        }

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
    /* root is const false -> unsat */
    if (!BTOR_COUNT_STACK (candidates))
    {
      res = 0;
      goto DONE;
    }

    slv->max_score = compute_sls_score_formula (btor, slv->score);
    slv->max_move  = BTOR_SLS_MOVE_DONE;
    slv->max_gw    = -1;

    if (btor_get_opt (btor, BTOR_OPT_SLS_MOVE_RAND_WALK)
        && btor_pick_with_prob_rng (
               &btor->rng,
               btor_get_opt (btor, BTOR_OPT_SLS_MOVE_RAND_WALK_PROB)))
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
  BtorBitVector *ass;
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
DONE:
  btor_init_node_hash_table_iterator (&it, slv->max_cans);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_free_bv (btor->mm, btor_next_data_hash_table_iterator (&it)->as_ptr);
  btor_delete_ptr_hash_table (slv->max_cans);
  slv->max_cans = 0;
  BTOR_RELEASE_STACK (btor->mm, candidates);
  return res;
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

static BtorSLSSolver *
clone_sls_solver (Btor *clone, BtorSLSSolver *slv, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (exp_map);

  int i;
  BtorSLSSolver *res;
  BtorSLSMove *m, *cm;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorSLSSolver));

  res->btor  = clone;
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
delete_sls_solver (BtorSLSSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;
  BtorHashTableIterator it;
  BtorSLSMove *m;

  btor = slv->btor;

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
static BtorSolverResult
sat_sls_solver (BtorSLSSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  int j, max_steps;
  BtorSolverResult sat_result;
  int nmoves;
  BtorNode *root;
  BtorPtrHashBucket *b;
  BtorSLSConstrData *d;
  BtorHashTableIterator it;
  Btor *btor;

  btor   = slv->btor;
  nmoves = 0;

  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  sat_result = btor_simplify (btor);
  BTOR_ABORT (btor->ufs->count != 0
                  || (!btor_get_opt (btor, BTOR_OPT_BETA_REDUCE_ALL)
                      && btor->lambdas->count != 0),
              "sls engine supports QF_BV only");

  if (btor->inconsistent) goto UNSAT;

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  slv->api.generate_model ((BtorSolver *) slv, false, true);

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
      sat_result = BTOR_RESULT_UNKNOWN;
      goto DONE;
    }

    /* compute initial sls score */
    btor_compute_sls_scores (btor, slv->score);

    if (compute_sls_score_formula (btor, slv->score) == -1.0)
    {
      sat_result = BTOR_RESULT_SAT;
      goto SAT;
    }

    for (j = 0, max_steps = BTOR_SLS_MAXSTEPS (slv->stats.restarts + 1);
         !btor_get_opt (btor, BTOR_OPT_SLS_USE_RESTARTS) || j < max_steps;
         j++)
    {
      if (btor_terminate_btor (btor))
      {
        sat_result = BTOR_RESULT_UNKNOWN;
        goto DONE;
      }

      if (!move (btor, nmoves)) goto UNSAT;
      nmoves += 1;

      if (compute_sls_score_formula (btor, slv->score) == -1.0)
      {
        sat_result = BTOR_RESULT_SAT;
        goto SAT;
      }
    }

    /* restart */
    slv->api.generate_model ((BtorSolver *) slv, false, true);
    btor_delete_ptr_hash_table (slv->score);
    slv->score = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
    slv->stats.restarts += 1;
  }

SAT:
  assert (sat_result == BTOR_RESULT_SAT);
  goto DONE;

UNSAT:
  sat_result = BTOR_RESULT_UNSAT;

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
generate_model_sls_solver (BtorSLSSolver *slv,
                           bool model_for_all_nodes,
                           bool reset)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;

  btor = slv->btor;

  if (!reset && btor->bv_model) return;
  btor_init_bv_model (btor, &btor->bv_model);
  btor_init_fun_model (btor, &btor->fun_model);
  btor_generate_model (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

static void
print_stats_sls_solver (BtorSLSSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;

  btor = slv->btor;

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
print_time_stats_sls_solver (BtorSLSSolver *slv)
{
  (void) slv;
}

BtorSolver *
btor_new_sls_solver (Btor *btor)
{
  assert (btor);

  BtorSLSSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind = BTOR_SLS_SOLVER_KIND;
  slv->btor = btor;

  slv->api.clone          = (BtorSolverClone) clone_sls_solver;
  slv->api.delet          = (BtorSolverDelete) delete_sls_solver;
  slv->api.sat            = (BtorSolverSat) sat_sls_solver;
  slv->api.generate_model = (BtorSolverGenerateModel) generate_model_sls_solver;
  slv->api.print_stats    = (BtorSolverPrintStats) print_stats_sls_solver;
  slv->api.print_time_stats =
      (BtorSolverPrintTimeStats) print_time_stats_sls_solver;

  BTOR_MSG (btor->msg, 1, "enabled sls engine");

  return (BtorSolver *) slv;
}

/*------------------------------------------------------------------------*/

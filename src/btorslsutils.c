/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslsutils.h"

#include "btorbv.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btornode.h"
#include "utils/btorutil.h"

#define BTOR_SLS_SCORE_CFACT 0.5     /* same as in Z3 (c1) */
#define BTOR_SLS_SCORE_F_CFACT 0.025 /* same as in Z3 (c3) */

/* ==========================================================================
 * SLS score computation
 * ==========================================================================
 *
 *  A(x) .... current assignment of expression x
 *
 *  Boolean variable:
 *  -----------------
 *    score (e) = A(e)
 *
 *  Bit-width bw >= 1:
 *  ------------------
 *
 *    score (e0_[bw] /\ e1_[bw]) =
 *        1/2 * (score (e0) + score (e1))
 *
 *    score (-(-e0_[bw] /\ ... /\ -e1_[bw])) =
 *        max (score (-e0), score (-e1))
 *
 *    score (e0_[bw] = e1_[bw]) =
 *        (A(e0) == A(e1))
 *        ? 1.0
 *        : c1 * (1 - (h (A(e0), A(e1)) / bw)
 *
 *    score (e0_[bw] != e1_[bw]) =
 *        (A (e0) == A (e1)
 *        ? 0.0
 *        : 1.0
 *
 *    s (e0[bw] < e1[bw]) =
 *        (A(e0) < A(e1))
 *        ? 1.0
 *        : c1 * (1 - (min number of bits to flip s.t. e0 < e1) / bw)
 *
 * ========================================================================== */

static uint32_t
hamming_distance (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (btor_bv_get_width (bv1) == btor_bv_get_width (bv2));
#ifndef BTOR_USE_GMP
  assert (btor_bv_get_len (bv1) == btor_bv_get_len (bv2));
#endif

  uint32_t res, bw;
  BtorBitVector *bv, *bvdec = 0, *zero, *ones, *tmp;

  bw   = btor_bv_get_width (bv1);
  zero = btor_bv_new (btor->mm, bw);
  ones = btor_bv_ones (btor->mm, bw);
  bv   = btor_bv_xor (btor->mm, bv1, bv2);
  for (res = 0; !btor_bv_is_zero (bv); res++)
  {
    bvdec = btor_bv_add (btor->mm, bv, ones);
    tmp   = bv;
    bv    = btor_bv_and (btor->mm, bv, bvdec);
    btor_bv_free (btor->mm, tmp);
    btor_bv_free (btor->mm, bvdec);
  }
  btor_bv_free (btor->mm, bv);
  btor_bv_free (btor->mm, ones);
  btor_bv_free (btor->mm, zero);
  return res;
}

// TODO find a better heuristic this might be too expensive
// this is not necessarily the actual minimum, but the minimum if you flip
// bits in bv1 s.t. bv1 < bv2 (if bv2 is 0, we need to flip 1 bit in bv2, too,
// which we do not consider to prevent negative scores)
static uint32_t
min_flip (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (btor_bv_get_width (bv1) == btor_bv_get_width (bv2));
#ifndef BTOR_USE_GMP
  assert (btor_bv_get_len (bv1) == btor_bv_get_len (bv2));
#endif

  uint32_t i, j, res, bw;
  BtorBitVector *tmp;

  if (btor_bv_is_zero (bv2))
    res = hamming_distance (btor, bv1, bv2);
  else
  {
    tmp = btor_bv_copy (btor->mm, bv1);
    bw  = btor_bv_get_width (tmp);
    for (res = 0, i = 0, j = bw - 1; i < bw; i++, j--)
    {
      if (!btor_bv_get_bit (tmp, j)) continue;
      res += 1;
      btor_bv_set_bit (tmp, j, 0);
      if (btor_bv_compare (tmp, bv2) < 0) break;
    }
    if (btor_bv_is_zero (bv2)) res += 1;
    btor_bv_free (btor->mm, tmp);
  }
  assert (res <= btor_bv_get_width (bv1));
  return res;
}

static uint32_t
min_flip_inv (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (btor_bv_get_width (bv1) == btor_bv_get_width (bv2));
#ifndef BTOR_USE_GMP
  assert (btor_bv_get_len (bv1) == btor_bv_get_len (bv2));
#endif

  uint32_t i, j, res, bw;
  BtorBitVector *tmp;

  tmp = btor_bv_copy (btor->mm, bv1);
  bw  = btor_bv_get_width (tmp);
  for (res = 0, i = 0, j = bw - 1; i < bw; i++, j--)
  {
    if (btor_bv_get_bit (tmp, j)) continue;
    res += 1;
    btor_bv_set_bit (tmp, j, 1);
    if (btor_bv_compare (tmp, bv2) >= 0) break;
  }
  btor_bv_free (btor->mm, tmp);
  return res;
}

double
btor_slsutils_compute_score_node (Btor *btor,
                                  BtorIntHashTable *bv_model,
                                  BtorIntHashTable *fun_model,
                                  BtorIntHashTable *score,
                                  BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score);
  assert (exp);
  assert (btor_node_bv_get_width (btor, exp) == 1);

  double res, s0, s1;
  BtorNode *real_exp;
  BtorBitVector *bv0, *bv1;
#ifndef NBTORLOG
  BtorMemMgr *mm;
  char *a0, *a1;
  mm = btor->mm;
#endif

  res      = 0.0;
  real_exp = btor_node_real_addr (exp);

  BTORLOG (3, "");
  BTORLOG (3, "*** compute sls score for: %s", btor_util_node2string (exp));

  if (btor_node_is_bv_and (real_exp))
  {
    /* ---------------------------------------------------------------------- */
    /* OR                                                                     */
    /* ---------------------------------------------------------------------- */
    if (btor_node_is_inverted (exp))
    {
      assert (btor_hashint_map_contains (score,
                                         -btor_node_get_id ((real_exp->e[0]))));
      assert (btor_hashint_map_contains (score,
                                         -btor_node_get_id ((real_exp->e[1]))));
      s0 = btor_hashint_map_get (score, -btor_node_get_id ((real_exp->e[0])))
               ->as_dbl;
      s1 = btor_hashint_map_get (score, -btor_node_get_id ((real_exp->e[1])))
               ->as_dbl;
#ifndef NBTORLOG
      if (btor_opt_get (btor, BTOR_OPT_LOGLEVEL) >= 2)
      {
        a0 = btor_bv_to_char (
            btor->mm,
            btor_model_get_bv_aux (
                btor, bv_model, fun_model, btor_node_invert (real_exp->e[0])));
        a1 = btor_bv_to_char (
            btor->mm,
            btor_model_get_bv_aux (
                btor, bv_model, fun_model, btor_node_invert (real_exp->e[1])));
        BTORLOG (3, "      assignment e[0]: %s", a0);
        BTORLOG (3, "      assignment e[1]: %s", a1);
        btor_mem_freestr (mm, a0);
        btor_mem_freestr (mm, a1);
        BTORLOG (3, "      sls score e[0]: %f", s0);
        BTORLOG (3, "      sls score e[1]: %f", s1);
      }
#endif
      res = s0 > s1 ? s0 : s1;
    }
    /* ---------------------------------------------------------------------- */
    /* AND                                                                    */
    /* ---------------------------------------------------------------------- */
    else
    {
      assert (btor_hashint_map_contains (score,
                                         btor_node_get_id ((real_exp->e[0]))));
      assert (btor_hashint_map_contains (score,
                                         btor_node_get_id ((real_exp->e[1]))));
      s0 = btor_hashint_map_get (score, btor_node_get_id ((real_exp->e[0])))
               ->as_dbl;
      s1 = btor_hashint_map_get (score, btor_node_get_id ((real_exp->e[1])))
               ->as_dbl;
#ifndef NBTORLOG
      if (btor_opt_get (btor, BTOR_OPT_LOGLEVEL) >= 2)
      {
        a0 = btor_bv_to_char (
            btor->mm,
            btor_model_get_bv_aux (
                btor, bv_model, fun_model, btor_node_invert (real_exp->e[0])));
        a1 = btor_bv_to_char (
            btor->mm,
            btor_model_get_bv_aux (
                btor, bv_model, fun_model, btor_node_invert (real_exp->e[1])));
        BTORLOG (3, "      assignment e[0]: %s", a0);
        BTORLOG (3, "      assignment e[1]: %s", a1);
        btor_mem_freestr (mm, a0);
        btor_mem_freestr (mm, a1);
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
  /* ------------------------------------------------------------------------ */
  /* EQ                                                                       */
  /* ------------------------------------------------------------------------ */
  else if (btor_node_is_bv_eq (real_exp))
  {
    bv0 = (BtorBitVector *) btor_model_get_bv_aux (
        btor, bv_model, fun_model, real_exp->e[0]);
    bv1 = (BtorBitVector *) btor_model_get_bv_aux (
        btor, bv_model, fun_model, real_exp->e[1]);
#ifndef NBTORLOG
    if (btor_opt_get (btor, BTOR_OPT_LOGLEVEL) >= 2)
    {
      a0 = btor_bv_to_char (
          btor->mm,
          btor_model_get_bv_aux (
              btor, bv_model, fun_model, btor_node_invert (real_exp->e[0])));
      a1 = btor_bv_to_char (
          btor->mm,
          btor_model_get_bv_aux (
              btor, bv_model, fun_model, btor_node_invert (real_exp->e[1])));
      BTORLOG (3, "      assignment e[0]: %s", a0);
      BTORLOG (3, "      assignment e[1]: %s", a1);
      btor_mem_freestr (mm, a0);
      btor_mem_freestr (mm, a1);
    }
#endif
    if (btor_node_is_inverted (exp))
      res = !btor_bv_compare (bv0, bv1) ? 0.0 : 1.0;
    else
      res = !btor_bv_compare (bv0, bv1)
                ? 1.0
                : BTOR_SLS_SCORE_CFACT
                      * (1.0
                         - hamming_distance (btor, bv0, bv1)
                               / (double) btor_bv_get_width (bv0));
  }
  /* ------------------------------------------------------------------------ */
  /* ULT                                                                      */
  /* ------------------------------------------------------------------------ */
  else if (btor_node_is_bv_ult (real_exp))
  {
    bv0 = (BtorBitVector *) btor_model_get_bv_aux (
        btor, bv_model, fun_model, real_exp->e[0]);
    bv1 = (BtorBitVector *) btor_model_get_bv_aux (
        btor, bv_model, fun_model, real_exp->e[1]);
#ifndef NBTORLOG
    if (btor_opt_get (btor, BTOR_OPT_LOGLEVEL) >= 2)
    {
      a0 = btor_bv_to_char (
          btor->mm,
          btor_model_get_bv_aux (
              btor, bv_model, fun_model, btor_node_invert (real_exp->e[0])));
      a1 = btor_bv_to_char (
          btor->mm,
          btor_model_get_bv_aux (
              btor, bv_model, fun_model, btor_node_invert (real_exp->e[1])));
      BTORLOG (3, "      assignment e[0]: %s", a0);
      BTORLOG (3, "      assignment e[1]: %s", a1);
      btor_mem_freestr (mm, a0);
      btor_mem_freestr (mm, a1);
    }
#endif
    if (btor_node_is_inverted (exp))
      res = btor_bv_compare (bv0, bv1) >= 0
                ? 1.0
                : BTOR_SLS_SCORE_CFACT
                      * (1.0
                         - min_flip_inv (btor, bv0, bv1)
                               / (double) btor_bv_get_width (bv0));
    else
      res = btor_bv_compare (bv0, bv1) < 0
                ? 1.0
                : BTOR_SLS_SCORE_CFACT
                      * (1.0
                         - min_flip (btor, bv0, bv1)
                               / (double) btor_bv_get_width (bv0));
  }
  /* ------------------------------------------------------------------------ */
  /* other BOOLEAN                                                            */
  /* ------------------------------------------------------------------------ */
  else
  {
    assert (btor_node_bv_get_width (btor, real_exp) == 1);
#ifndef NBTORLOG
    if (btor_opt_get (btor, BTOR_OPT_LOGLEVEL) >= 2)
    {
      a0 = btor_bv_to_char (
          btor->mm,
          btor_model_get_bv_aux (
              btor, bv_model, fun_model, btor_node_invert (exp)));
      BTORLOG (3, "      assignment : %s", a0);
      btor_mem_freestr (mm, a0);
    }
#endif
    res = btor_bv_get_bit (((BtorBitVector *) btor_model_get_bv_aux (
                               btor, bv_model, fun_model, exp)),
                           0);
  }

  BTORLOG (3, "      sls score : %f", res);
  assert (res >= 0.0 && res <= 1.0);
  return res;
}

static double
recursively_compute_sls_score_node (Btor *btor,
                                    BtorIntHashTable *bv_model,
                                    BtorIntHashTable *fun_model,
                                    BtorIntHashTable *score,
                                    BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score);
  assert (exp);

  uint32_t i;
  double res;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack stack;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorMemMgr *mm;

  res = 0.0;
  assert (btor_node_is_bv_eq (exp) || btor_node_is_bv_ult (exp)
          || btor_node_bv_get_width (btor, exp) == 1);

  if (btor_hashint_map_contains (score, btor_node_get_id (exp)))
    return btor_hashint_map_get (score, btor_node_get_id (exp))->as_dbl;

  mm = btor->mm;
  BTOR_INIT_STACK (mm, stack);
  mark = btor_hashint_map_new (mm);

  BTOR_PUSH_STACK (stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = btor_node_real_addr (cur);
    d        = btor_hashint_map_get (mark, real_cur->id);

    if ((d && d->as_int == 1)
        || btor_hashint_map_get (score, btor_node_get_id (cur)))
      continue;

    if (!d)
    {
      btor_hashint_map_add (mark, real_cur->id);
      BTOR_PUSH_STACK (stack, cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (stack, real_cur->e[i]);
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;

      if (btor_node_bv_get_width (btor, real_cur) != 1) continue;

      res = btor_slsutils_compute_score_node (
          btor, bv_model, fun_model, score, cur);

      assert (!btor_hashint_map_contains (score, btor_node_get_id (cur)));
      btor_hashint_map_add (score, btor_node_get_id (cur))->as_dbl = res;
    }
  }

  BTOR_RELEASE_STACK (stack);
  btor_hashint_map_delete (mark);

  assert (btor_hashint_map_contains (score, btor_node_get_id (exp)));
  assert (res == btor_hashint_map_get (score, btor_node_get_id (exp))->as_dbl);
  return res;
}

/* -------------------------------------------------------------------------- */

void
btor_slsutils_compute_sls_scores (Btor *btor,
                                  BtorIntHashTable *bv_model,
                                  BtorIntHashTable *fun_model,
                                  BtorIntHashTable *score)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP
          || btor_opt_get (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS);
  assert (bv_model);
  assert (fun_model);
  assert (score);

  uint32_t i;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack stack;
  BtorPtrHashTableIterator pit;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorMemMgr *mm;

  BTORLOG (3, "");
  BTORLOG (3, "**** compute sls scores ***");

  mm = btor->mm;
  BTOR_INIT_STACK (mm, stack);
  mark = btor_hashint_map_new (mm);

  /* collect roots */
  btor_iter_hashptr_init (&pit, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&pit, btor->assumptions);
  while (btor_iter_hashptr_has_next (&pit))
    BTOR_PUSH_STACK (stack, btor_iter_hashptr_next (&pit));

  /* compute score */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = btor_node_real_addr (cur);
    d        = btor_hashint_map_get (mark, real_cur->id);

    if ((d && d->as_int == 1)
        || btor_hashint_map_contains (score, btor_node_get_id (cur)))
      continue;

    if (!d)
    {
      btor_hashint_map_add (mark, real_cur->id);
      BTOR_PUSH_STACK (stack, cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (stack, real_cur->e[i]);
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;
      if (btor_node_bv_get_width (btor, real_cur) != 1) continue;
      (void) recursively_compute_sls_score_node (
          btor, bv_model, fun_model, score, cur);
      (void) recursively_compute_sls_score_node (
          btor, bv_model, fun_model, score, btor_node_invert (cur));
    }
  }

  BTOR_RELEASE_STACK (stack);
  btor_hashint_map_delete (mark);
}

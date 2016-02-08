/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorprop.h"
#include "btorabort.h"
#include "btorbitvec.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btoropt.h"
#include "btorsls.h"  // currently needed, TODO maybe get rid of in the future

#include "utils/btorhashptr.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"

#include <math.h>

/*------------------------------------------------------------------------*/

#define BTOR_PROP_MAXSTEPS_CFACT 100
#define BTOR_PROP_MAXSTEPS(i) \
  (BTOR_PROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BTOR_PROP_SELECT_CFACT 20

/*------------------------------------------------------------------------*/

static inline int
select_path_non_const (BtorNode *exp)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (exp->arity <= 2);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp->e[0]))
          || (exp->arity > 1
              && !BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp->e[1]))));

  int i, eidx;

  for (i = 0, eidx = -1; i < exp->arity; i++)
    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp->e[i])))
    {
      eidx = i ? 0 : 1;
      break;
    }
  assert (exp->arity == 1 || !BTOR_IS_BV_CONST_NODE (exp->e[i ? 0 : 1]));
  return eidx;
}

static inline int
select_path_random (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return (int) btor_pick_rand_rng (&btor->rng, 0, exp->arity - 1);
}

static inline int
select_path_add (Btor *btor,
                 BtorNode *add,
                 BtorBitVector *bvadd,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (add);
  assert (BTOR_IS_REGULAR_NODE (add));
  assert (bvadd);
  assert (bve);

  (void) bvadd;
  (void) bve;

  int eidx;

  eidx = select_path_non_const (add);
  if (eidx == -1) eidx = select_path_random (btor, add);
  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (add));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (add->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (add->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_and (Btor *btor,
                 BtorNode *and,
                 BtorBitVector *bvand,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (and);
  assert (BTOR_IS_REGULAR_NODE (and));
  assert (bvand);
  assert (bve);

  int i, eidx;
  BtorBitVector *tmp;

  (void) bvand;
  eidx = select_path_non_const (and);

  if (eidx == -1)
  {
    if (btor_get_exp_width (btor, and) == 1)
    {
      /* choose 0-branch if exactly one branch is 0, else choose randomly */
      for (i = 0; i < and->arity; i++)
        if (btor_is_zero_bv (bve[i])) eidx = eidx == -1 ? i : -1;
      if (eidx == -1) eidx = select_path_random (btor, and);
    }
    else if (btor->options.prop_use_full_path.val == 1)
    {
      /* 1) all bits set in bvand must be set in both inputs, but
       * 2) all bits NOT set in bvand can be cancelled out by either or both
       * -> choose single input that violates 1)
       * -> else choose randomly */
      for (i = 0; i < and->arity; i++)
      {
        tmp = btor_and_bv (btor->mm, bvand, bve[i]);
        if (btor_compare_bv (tmp, bvand)) eidx = eidx == -1 ? i : -1;
        btor_free_bv (btor->mm, tmp);
      }
    }
    if (eidx == -1) eidx = select_path_random (btor, and);
  }

  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (and));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (and->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (and->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_eq (Btor *btor,
                BtorNode *eq,
                BtorBitVector *bveq,
                BtorBitVector **bve)
{
  assert (btor);
  assert (eq);
  assert (BTOR_IS_REGULAR_NODE (eq));
  assert (bveq);
  assert (bve);

  (void) bveq;
  (void) bve;

  int eidx;
  eidx = select_path_non_const (eq);
  if (eidx == -1) eidx = select_path_random (btor, eq);
  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (eq));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (eq->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (eq->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_ult (Btor *btor,
                 BtorNode *ult,
                 BtorBitVector *bvult,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (ult);
  assert (BTOR_IS_REGULAR_NODE (ult));
  assert (bvult);
  assert (bve);

  int eidx;
  BtorBitVector *bvmax;

  eidx = select_path_non_const (ult);

  if (eidx == -1)
  {
    if (btor->options.prop_use_full_path.val == 1)
    {
      bvmax = btor_ones_bv (btor->mm, bve[0]->width);
      if (btor_is_one_bv (bvult))
      {
        /* 1...1 < bve[1] */
        if (!btor_compare_bv (bve[0], bvmax)) eidx = 0;
        /* bve[0] < 0 */
        if (btor_is_zero_bv (bve[1])) eidx = eidx == -1 ? 1 : -1;
      }
      btor_free_bv (btor->mm, bvmax);
    }
    if (eidx == -1) eidx = select_path_random (btor, ult);
  }

  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (ult));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (ult->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (ult->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_sll (Btor *btor,
                 BtorNode *sll,
                 BtorBitVector *bvsll,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (sll);
  assert (BTOR_IS_REGULAR_NODE (sll));
  assert (bvsll);
  assert (bve);

  int eidx;
  uint64_t i, j, shift;

  eidx = select_path_non_const (sll);

  if (eidx == -1)
  {
    if (btor->options.prop_use_full_path.val == 1)
    {
      shift = btor_bv_to_uint64_bv (bve[1]);
      /* bve[1] and number of LSB 0-bits in bvsll must match */
      for (i = 0; i < shift; i++)
        if (btor_get_bit_bv (bvsll, i))
        {
          eidx = 1;
          goto DONE;
        }
      /* bve[0] and bvsll (except for the bits shifted out) must match */
      for (i = 0, j = shift; i < bvsll->width - j; i++)
        if (btor_get_bit_bv (bve[0], i) != btor_get_bit_bv (bvsll, j + i))
        {
          eidx = eidx == -1 ? 0 : -1;
          break;
        }
    }
    if (eidx == -1) eidx = select_path_random (btor, sll);
  }
DONE:
  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (sll));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (sll->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (sll->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_srl (Btor *btor,
                 BtorNode *srl,
                 BtorBitVector *bvsrl,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (srl);
  assert (BTOR_IS_REGULAR_NODE (srl));
  assert (bvsrl);
  assert (bve);

  int eidx;
  uint64_t i, j, shift;

  eidx = select_path_non_const (srl);

  if (eidx == -1)
  {
    if (btor->options.prop_use_full_path.val == 1)
    {
      shift = btor_bv_to_uint64_bv (bve[1]);
      /* bve[1] and number of MSB 0-bits in bvsrl must match */
      for (i = 0; i < shift; i++)
        if (btor_get_bit_bv (bvsrl, bvsrl->width - 1 - i))
        {
          eidx = 1;
          goto DONE;
        }
      /* bve[0] and bvsrl (except for the bits shifted out) must match */
      for (i = 0, j = shift; i < bvsrl->width - j; i++)
        if (btor_get_bit_bv (bve[0], bve[0]->width - 1 - i)
            != btor_get_bit_bv (bvsrl, bvsrl->width - 1 - (j + i)))
        {
          eidx = eidx == -1 ? 0 : -1;
          break;
        }
    }
    if (eidx == -1) eidx = select_path_random (btor, srl);
  }
DONE:
  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (srl));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (srl->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (srl->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_mul (Btor *btor,
                 BtorNode *mul,
                 BtorBitVector *bvmul,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (mul);
  assert (BTOR_IS_REGULAR_NODE (mul));
  assert (bvmul);
  assert (bve);

  (void) bvmul;
  (void) bve;

  uint32_t i, j;
  int eidx, lsbve0, lsbve1;
  bool iszerobve0, iszerobve1;

  eidx = select_path_non_const (mul);

  if (eidx == -1)
  {
    if (btor->options.prop_use_full_path.val == 1)
    {
      iszerobve0 = btor_is_zero_bv (bve[0]);
      iszerobve1 = btor_is_zero_bv (bve[1]);

      lsbve0 = btor_get_bit_bv (bve[0], 0);
      lsbve1 = btor_get_bit_bv (bve[1], 0);

      /* either bve[0] or bve[1] are 0 but bvmul > 0 */
      if ((iszerobve0 || iszerobve1) && !btor_is_zero_bv (bvmul))
      {
        if (iszerobve0) eidx = 0;
        if (iszerobve1) eidx = eidx == -1 ? 1 : -1;
      }
      /* bvmul is odd but either bve[0] or bve[1] are even */
      else if (btor_get_bit_bv (bvmul, 0) && (!lsbve0 || !lsbve1))
      {
        if (!lsbve0) eidx = 0;
        if (!lsbve1) eidx = eidx == -1 ? 1 : -1;
      }
      /* number of 0-LSBs in bvmul < number of 0-LSBs in bve[0|1] */
      else
      {
        for (i = 0; i < bvmul->width; i++)
          if (btor_get_bit_bv (bvmul, i)) break;
        for (j = 0; j < bve[0]->width; j++)
          if (btor_get_bit_bv (bve[0], j)) break;
        if (i < j) eidx = 0;
        for (j = 0; j < bve[1]->width; j++)
          if (btor_get_bit_bv (bve[1], j)) break;
        if (i < j) eidx = eidx == -1 ? 1 : -1;
      }
    }
    if (eidx == -1) eidx = select_path_random (btor, mul);
  }
  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (mul));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (mul->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (mul->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_udiv (Btor *btor,
                  BtorNode *udiv,
                  BtorBitVector *bvudiv,
                  BtorBitVector **bve)
{
  assert (btor);
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);

  int eidx;
  int cmp_udiv_max;
  BtorBitVector *bvmax, *up, *lo, *tmp;

  eidx = select_path_non_const (udiv);

  if (eidx == -1)
  {
    if (btor->options.prop_use_full_path.val == 1)
    {
      bvmax        = btor_ones_bv (btor->mm, bve[0]->width);
      cmp_udiv_max = btor_compare_bv (bvudiv, bvmax);

      /* bve[0] / bve[1] = 1...1 -> choose e[1]
       *   + 1...1 / 0 = 1...1
       *   + 1...1 / 1 = 1...1
       *   + x...x / 0 = 1...1 */
      if (!cmp_udiv_max)
        eidx = 1;
      else
      {
        /* 1...1 / e[0] = 0 -> choose e[0] */
        if (btor_is_zero_bv (bvudiv) && !btor_compare_bv (bve[0], bvmax))
          eidx = 0;
        /* bve[0] < bvudiv -> choose e[0] */
        else if (btor_compare_bv (bve[0], bvudiv) < 0)
          eidx = 0;
        else
        {
          up  = btor_udiv_bv (btor->mm, bve[0], bvudiv);
          lo  = btor_inc_bv (btor->mm, bvudiv);
          tmp = btor_udiv_bv (btor->mm, bve[0], lo);
          btor_free_bv (btor->mm, lo);
          lo = btor_inc_bv (btor->mm, tmp);

          if (btor_compare_bv (lo, up) > 0) eidx = 0;
          btor_free_bv (btor->mm, up);
          btor_free_bv (btor->mm, lo);
          btor_free_bv (btor->mm, tmp);
        }

        /* e[0] / 0 != 1...1 -> choose e[1] */
        if (btor_is_zero_bv (bve[1])
            || btor_is_umulo_bv (btor->mm, bve[1], bvudiv))
          eidx = eidx == -1 ? 1 : -1;
      }
      btor_free_bv (btor->mm, bvmax);
    }
    if (eidx == -1) eidx = select_path_random (btor, udiv);
  }

  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (udiv));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (udiv->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (udiv->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_urem (Btor *btor,
                  BtorNode *urem,
                  BtorBitVector *bvurem,
                  BtorBitVector **bve)
{
  assert (btor);
  assert (urem);
  assert (BTOR_IS_REGULAR_NODE (urem));
  assert (bvurem);
  assert (bve);

  int eidx;
  BtorBitVector *bvmax, *sub, *tmp;

  eidx = select_path_non_const (urem);

  if (eidx == -1)
  {
    if (btor->options.prop_use_full_path.val == 1)
    {
      bvmax = btor_ones_bv (btor->mm, bve[0]->width);
      sub   = btor_sub_bv (btor->mm, bve[0], bvurem);
      tmp   = btor_dec_bv (btor->mm, bve[0]);

      /* bvurem = 1...1 -> bve[0] = 1...1 and bve[1] = 0...0 */
      if (!btor_compare_bv (bvurem, bvmax))
      {
        if (!btor_is_zero_bv (bve[1])) eidx = 1;
        if (btor_compare_bv (bve[0], bvmax)) eidx = eidx == -1 ? 0 : -1;
      }
      /* bvurem > 0 and bve[1] = 1 */
      else if (!btor_is_zero_bv (bvurem) && btor_is_one_bv (bve[1]))
      {
        eidx = 1;
      }
      /* 0 < bve[1] <= bvurem */
      else if (!btor_is_zero_bv (bve[1])
               && btor_compare_bv (bve[1], bvurem) <= 0)
      {
        eidx = eidx == -1 ? 1 : -1;
      }
      /* bve[0] < bvurem or
       * bve[0] > bvurem and bve[0] - bvurem <= bvurem or
       *                 and bve[0] - 1 = bvurem */
      else if (btor_compare_bv (bve[0], bvurem) < 0
               || (btor_compare_bv (bve[0], bvurem) > 0
                   && (btor_compare_bv (sub, bvurem) <= 0
                       || !btor_compare_bv (tmp, bvurem))))
      {
        eidx = 0;
      }

      btor_free_bv (btor->mm, tmp);
      btor_free_bv (btor->mm, bvmax);
      btor_free_bv (btor->mm, sub);
    }

    if (eidx == -1) eidx = select_path_random (btor, urem);
  }

  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (urem));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (urem->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (urem->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_concat (Btor *btor,
                    BtorNode *concat,
                    BtorBitVector *bvconcat,
                    BtorBitVector **bve)
{
  assert (btor);
  assert (concat);
  assert (BTOR_IS_REGULAR_NODE (concat));
  assert (bvconcat);
  assert (bve);

  int eidx;
  BtorBitVector *tmp;

  eidx = select_path_non_const (concat);

  if (eidx == -1)
  {
    if (btor->options.prop_use_full_path.val == 1)
    {
      /* bve[0] o bve[1] = bvconcat
       * -> bve[0] resp. bve[1] must match with bvconcat */
      tmp = btor_slice_bv (btor->mm,
                           bvconcat,
                           bvconcat->width - 1,
                           bvconcat->width - bve[0]->width);
      if (btor_compare_bv (tmp, bve[0])) eidx = 0;
      btor_free_bv (btor->mm, tmp);
      tmp = btor_slice_bv (btor->mm, bvconcat, bve[1]->width - 1, 0);
      if (btor_compare_bv (tmp, bve[1])) eidx = eidx == -1 ? 1 : -1;
      btor_free_bv (btor->mm, tmp);
    }

    if (eidx == -1) eidx = select_path_random (btor, concat);
  }

  assert (eidx >= 0);
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (concat));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (concat->e[0]), a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (concat->e[1]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_slice (Btor *btor,
                   BtorNode *slice,
                   BtorBitVector *bvslice,
                   BtorBitVector **bve)
{
  assert (btor);
  assert (slice);
  assert (BTOR_IS_REGULAR_NODE (slice));
  assert (bvslice);
  assert (bve);

  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (slice->e[0])));

  (void) btor;
  (void) slice;
  (void) bvslice;
  (void) bve;
#ifndef NDEBUG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (slice));
  a = btor_bv_to_char_bv (btor->mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (slice->e[0]), a);
  btor_freestr (btor->mm, a);
  BTORLOG (2, "    * chose: 0");
#endif

  return 0;
}

/*------------------------------------------------------------------------*/

#define BTOR_INC_REC_CONF_STATS(btor, inc)                      \
  do                                                            \
  {                                                             \
    if (btor->options.engine.val == BTOR_ENGINE_PROP)           \
      BTOR_PROP_SOLVER (btor)->stats.move_prop_rec_conf += inc; \
    else                                                        \
      BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += inc;  \
  } while (0)

#define BTOR_INC_NON_REC_CONF_STATS(btor, inc)                      \
  do                                                                \
  {                                                                 \
    if (btor->options.engine.val == BTOR_ENGINE_PROP)               \
      BTOR_PROP_SOLVER (btor)->stats.move_prop_non_rec_conf += inc; \
    else                                                            \
      BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += inc;  \
  } while (0)

static inline BtorBitVector *
non_rec_conf (
    Btor *btor, BtorBitVector *bve, BtorBitVector *bvexp, int eidx, char *op)
{
  assert (btor);
  assert (bve);
  assert (bvexp);
  assert (op);

  (void) bve;
  (void) bvexp;
  (void) eidx;
  (void) op;

#ifndef NDEBUG
  char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
  char *sbvexp = btor_bv_to_char_bv (btor->mm, bvexp);
  if (eidx)
    BTORLOG (2, "prop CONFLICT: %s := %s %s x", sbvexp, sbve, op);
  else
    BTORLOG (2, "prop CONFLICT: %s := x %s %s", sbvexp, op, sbve);
  btor_freestr (btor->mm, sbve);
  btor_freestr (btor->mm, sbvexp);
#endif
  BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
  return 0;
}

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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
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

  char *sbvadd = btor_bv_to_char_bv (btor->mm, bvadd);
  char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
  char *sres   = btor_bv_to_char_bv (btor->mm, res);
  if (eidx)
    BTORLOG (3,
             "prop (e[%d]): %s: %s := %s + %s",
             eidx,
             node2string (add),
             sbvadd,
             eidx ? sbve : sres,
             eidx ? sres : sbve);
  btor_freestr (btor->mm, sbvadd);
  btor_freestr (btor->mm, sbve);
  btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        btor_free_bv (mm, res);
        res = non_rec_conf (btor, bve, bvand, eidx, "AND");
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

  BTOR_INC_REC_CONF_STATS (btor, isreccon);

#ifndef NDEBUG
  if (!iscon)
  {
    if (eidx)
      tmpdbg = btor_and_bv (mm, bve, res);
    else
      tmpdbg = btor_and_bv (mm, res, bve);
    assert (!btor_compare_bv (tmpdbg, bvand));
    btor_free_bv (mm, tmpdbg);

    char *sbvand = btor_bv_to_char_bv (btor->mm, bvand);
    char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
    char *sres   = btor_bv_to_char_bv (btor->mm, res);
    if (eidx)
      BTORLOG (3,
               "prop (e[%d]): %s: %s := %s AND %s",
               eidx,
               node2string (and),
               sbvand,
               eidx ? sbve : sres,
               eidx ? sres : sbve);
    btor_freestr (btor->mm, sbvand);
    btor_freestr (btor->mm, sbve);
    btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
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

  char *sbveq = btor_bv_to_char_bv (btor->mm, bveq);
  char *sbve  = btor_bv_to_char_bv (btor->mm, bve);
  char *sres  = btor_bv_to_char_bv (btor->mm, res);
  if (eidx)
    BTORLOG (3,
             "prop (e[%d]): %s: %s := %s = %s",
             eidx,
             node2string (eq),
             sbveq,
             eidx ? sbve : sres,
             eidx ? sres : sbve);
  btor_freestr (btor->mm, sbveq);
  btor_freestr (btor->mm, sbve);
  btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (ult);
  assert (BTOR_IS_REGULAR_NODE (ult));
  assert (bvult);
  assert (bvult->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (ult->e[eidx])));

  bool isult;
  uint32_t bw;
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

  res = 0;

  if (eidx)
  {
    /* conflict: 1...1 < e[1] */
    if (!btor_compare_bv (bve, bvmax) && isult)
    {
#ifndef NDEBUG
      iscon = 1;
#endif
      /* check for non-recoverable conflict */
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = non_rec_conf (btor, bve, bvult, eidx, "<");
      }
      else if (isult)
      {
        res = btor_new_random_range_bv (mm, &btor->rng, bw, one, bvmax);
        BTOR_INC_REC_CONF_STATS (btor, 1);
      }
      else
      {
        // FIXME not reachable
        tmp = btor_sub_bv (mm, bvmax, one);
        res = btor_new_random_range_bv (mm, &btor->rng, bw, zero, tmp);
        btor_free_bv (mm, tmp);
        BTOR_INC_REC_CONF_STATS (btor, 1);
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = non_rec_conf (btor, bve, bvult, eidx, "<");
      }
      else if (!isult)
      {
        // FIXME not reachable
        res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, one, bvmax);
        BTOR_INC_REC_CONF_STATS (btor, 1);
      }
      else
      {
        tmp = btor_sub_bv (btor->mm, bvmax, one);
        res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, zero, tmp);
        btor_free_bv (btor->mm, tmp);
        BTOR_INC_REC_CONF_STATS (btor, 1);
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

    char *sbvult = btor_bv_to_char_bv (btor->mm, bvult);
    char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
    char *sres   = btor_bv_to_char_bv (btor->mm, res);
    if (eidx)
      BTORLOG (3,
               "prop (e[%d]): %s: %s := %s < %s",
               eidx,
               node2string (ult),
               eidx ? sbve : sres,
               eidx ? sres : sbve,
               sbvult);
    btor_freestr (btor->mm, sbvult);
    btor_freestr (btor->mm, sbve);
    btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (sll);
  assert (BTOR_IS_REGULAR_NODE (sll));
  assert (bvsll);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsll->width);
  assert (eidx || btor_log_2_util (bvsll->width) == bve->width);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (sll->e[eidx])));

  uint32_t i, j, ctz_bve, ctz_bvsll, shift, sbw;
  BtorNode *e;
  BtorBitVector *res, *tmp, *bvmax;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = sll->e[eidx ? 0 : 1];
  assert (e);

  res = 0;

  /* bve << e[1] = bvsll
   * -> identify possible shift value via zero LSB in bvsll
   *    (considering zero LSB in bve) */
  if (eidx)
  {
    sbw = btor_log_2_util (bvsll->width);

    /* 0...0 << e[1] = 0...0 -> choose res randomly */
    if (btor_is_zero_bv (bve) && btor_is_zero_bv (bvsll))
    {
    BVSLL_RANDOM_SHIFT:
      res = btor_new_random_bv (btor->mm, &btor->rng, sbw);
    }
    /* -> ctz(bve) > ctz (bvsll) -> conflict
     * -> shift = ctz(bvsll) - ctz(bve)
     *      -> if bvsll = 0 choose shift <= res < bw
     *      -> else res = shift
     *           + if all remaining shifted bits match
     *	   + and if res < bw
     * -> else conflict  */
    else
    {
      ctz_bve   = btor_get_num_trailing_zeros_bv (bve);
      ctz_bvsll = btor_get_num_trailing_zeros_bv (bvsll);
      if (ctz_bve <= ctz_bvsll)
      {
        shift = ctz_bvsll - ctz_bve;

        /* do not allow shift by bw -> conflict */
        if (shift > bvsll->width - 1)
        {
          assert (btor_is_zero_bv (bvsll));

          /* check for non-recoverable conflict */
          if (btor->options.engine.val == BTOR_ENGINE_SLS
              && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
            return non_rec_conf (btor, bve, bvsll, eidx, "<<");
#ifndef NDEBUG
          iscon = 1;
#endif
          BTOR_INC_REC_CONF_STATS (btor, 1);
          goto BVSLL_RANDOM_SHIFT;
        }
        /* x...x0 << e[1] = 0...0
         * -> choose random shift <= res < bw */
        else if (btor_is_zero_bv (bvsll))
        {
          bvmax = btor_ones_bv (btor->mm, sbw);
          tmp   = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
          res =
              btor_new_random_range_bv (btor->mm, &btor->rng, sbw, tmp, bvmax);
          btor_free_bv (btor->mm, bvmax);
          btor_free_bv (btor->mm, tmp);
        }
        else
        {
          /* check for conflict -> shifted bits must match */
          for (i = 0, j = shift, res = 0; i < bve->width - j; i++)
          {
            if (btor_get_bit_bv (bve, i) != btor_get_bit_bv (bvsll, j + i))
            {
            BVSLL_CONF1:
              /* check for non-recoverable conflict */
              if (btor->options.engine.val == BTOR_ENGINE_SLS
                  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
                return non_rec_conf (btor, bve, bvsll, eidx, "<<");
#ifndef NDEBUG
              iscon = 1;
#endif
              // FIXME this should be random res <= ctz_bvsll
              // res = btor_uint64_to_bv (
              //    mm, (uint64_t) ctz_bvsll, sbw);
              shift = ctz_bvsll;
              BTOR_INC_REC_CONF_STATS (btor, 1);
              break;
            }
          }

          res = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
        }
      }
      else
      {
        goto BVSLL_CONF1;
      }
#if 0
	  for (i = 0, oneidx = -1; i < bvsll->width; i++)
	    {
	      if (oneidx == -1 && btor_get_bit_bv (bve, i)) oneidx = i;
	      if (btor_get_bit_bv (bvsll, i)) break;
	    }
	  shift = oneidx == -1 ? i : i - oneidx;
	  shiftconf = i;
#ifndef NDEBUG
	  for (i = 0; i < shift; i++) assert (!btor_get_bit_bv (bvsll, i));
#endif

	  // FIXME this is correct for ctz(bve) > ctz(t) by accident
	  // due to unsignedness of variable 'shift', because the case
	  // shift > bvsll->width - 1 captures this (-shift in unsigned
	  // is greater than bw)
	  // better to be more explicit
	  // ctz(bve) = oneidx
	  // ctz(t) = i
	  // rules:
	  //  -> ctz(m) <= ctz(t) then res = ctz(t) - ctz(m)
	  //  -> ctz(m) > ctz(t) then conflict
	  // FIXME FIXME FIXME
	  /* check for conflict -> do not allow shift by bw */
	  if (shift > bvsll->width - 1)
	    {
	      assert (btor_is_zero_bv (bvsll));

	      /* check for non-recoverable conflict */
	      if (btor->options.engine.val == BTOR_ENGINE_SLS
		  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
		{
#ifndef NDEBUG
		  char *sbvsll = btor_bv_to_char_bv (btor->mm, bvsll);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := %s << x", sbvsll, sbve);
		  btor_freestr (btor->mm, sbvsll);
		  btor_freestr (btor->mm, sbve);
#endif
		  BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
		  return 0;
		}
#ifndef NDEBUG
	      iscon = 1;
#endif
	      BTOR_INC_REC_CONF_STATS (btor, 1);
	      goto BVSLL_RANDOM_SHIFT;
	    }
	  /* x...x0 << e[1] = 0...0 */
	  else if (btor_is_zero_bv (bvsll))
	    {
	      bvmax = btor_ones_bv (btor->mm, sbw);
	      tmp = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
	      res = btor_new_random_range_bv (
		  btor->mm, &btor->rng, sbw, tmp, bvmax);
	      btor_free_bv (btor->mm, bvmax);
	      btor_free_bv (btor->mm, tmp);
	    }
	  else
	    {
	      /* check for conflict -> shifted bits must match */
	      for (i = 0, j = shift, res = 0; i < bve->width - j; i++)
		{
		  if (btor_get_bit_bv (bve, i) != btor_get_bit_bv (bvsll, j+i))
		    {
		      /* check for non-recoverable conflict */
		      if (btor->options.engine.val == BTOR_ENGINE_SLS
			  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
			{
#ifndef NDEBUG
			  char *sbvsll = btor_bv_to_char_bv (btor->mm, bvsll);
			  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
			  BTORLOG (2, "prop CONFLICT: %s := %s << x",
				   sbvsll, sbve);
			  btor_freestr (btor->mm, sbvsll);
			  btor_freestr (btor->mm, sbve);
#endif
			  BTOR_SLS_SOLVER (
			      btor)->stats.move_prop_non_rec_conf += 1;
			  return 0;
			}
#ifndef NDEBUG
		      iscon = 1;
#endif
		      res = btor_uint64_to_bv (mm, (uint64_t) shiftconf, sbw);
		      BTOR_INC_REC_CONF_STATS (btor, 1);
		      break;
		    }
		}
	      if (!res) res = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
	    }
#endif
    }
  }
  /* e[0] << bve = bvsll
   * -> e[0] = bvsll >> bve
   *    set irrelevant MSBs (the ones that get shifted out) randomly */
  else
  {
    /* using uint64_t here is no problem
     * (max bit width currently handled by Boolector is INT_MAX) */
    shift = btor_bv_to_uint64_bv (bve);

    /* check for conflict -> the LSBs shifted must be zero */
    for (i = 0; i < shift; i++)
    {
      if (btor_get_bit_bv (bvsll, i))
      {
        /* check for non-recoverable conflict */
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
          return non_rec_conf (btor, bve, bvsll, eidx, "<<");
#ifndef NDEBUG
        iscon = 1;
#endif
        BTOR_INC_REC_CONF_STATS (btor, 1);
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

    char *sbvsll = btor_bv_to_char_bv (btor->mm, bvsll);
    char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
    char *sres   = btor_bv_to_char_bv (btor->mm, res);
    if (eidx)
      BTORLOG (3,
               "prop (e[%d]): %s: %s := %s << %s",
               eidx,
               node2string (sll),
               sbvsll,
               eidx ? sbve : sres,
               eidx ? sres : sbve);
    btor_freestr (btor->mm, sbvsll);
    btor_freestr (btor->mm, sbve);
    btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (srl);
  assert (BTOR_IS_REGULAR_NODE (srl));
  assert (bvsrl);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsrl->width);
  assert (eidx || btor_log_2_util (bvsrl->width) == bve->width);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (srl->e[eidx])));

  uint32_t i, j, clz_bve, clz_bvsrl, shift, sbw;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = srl->e[eidx ? 0 : 1];
  assert (e);

  res = 0;

  /* bve >> e[1] = bvsll
   * -> identify possible shift value via zero MSBs in bvsll
   *    (considering zero MSBs in bve) */
  if (eidx)
  {
    sbw = btor_log_2_util (bvsrl->width);

    /* 0...0 >> e[1] = 0...0 -> choose random res */
    if (btor_is_zero_bv (bve) && btor_is_zero_bv (bvsrl))
    {
    BVSRL_RANDOM_SHIFT:
      res = btor_new_random_bv (btor->mm, &btor->rng, sbw);
    }
    /* clz(bve) > clz(bvsrl) -> conflict
     * -> shift = clz(bvsrl) - clz(bve)
     *      -> if bvsrl = 0 choose shift <= res < bw
     *      -> else res = shift
     *           + if all remaining shifted bits match
     *           + and if res < bw
     * -> else conflict */
    else
    {
      clz_bve   = btor_get_num_leading_zeros_bv (bve);
      clz_bvsrl = btor_get_num_leading_zeros_bv (bvsrl);
      if (clz_bve <= clz_bvsrl)
      {
        shift = clz_bvsrl - clz_bve;

        /* do not allow shift by bw -> conflict */
        if (shift > bvsrl->width - 1)
        {
          /* check for non-recoverable conflict */
          if (btor->options.engine.val == BTOR_ENGINE_SLS
              && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
            return non_rec_conf (btor, bve, bvsrl, eidx, ">>");
#ifndef NDEBUG
          iscon = 1;
#endif
          BTOR_INC_REC_CONF_STATS (btor, 1);
          goto BVSRL_RANDOM_SHIFT;
        }
        /* x...x0 >> e[1] = 0...0
         * -> choose random shift <= res < bw */
        else if (btor_is_zero_bv (bvsrl))
        {
          bvmax = btor_ones_bv (btor->mm, sbw);
          tmp   = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
          res =
              btor_new_random_range_bv (btor->mm, &btor->rng, sbw, tmp, bvmax);
          btor_free_bv (btor->mm, bvmax);
          btor_free_bv (btor->mm, tmp);
        }
        else
        {
          /* check for conflict -> shifted bits must match */
          for (i = 0, j = shift, res = 0; i < bve->width - j; i++)
          {
            if (btor_get_bit_bv (bve, bve->width - 1 - i)
                != btor_get_bit_bv (bvsrl, bvsrl->width - 1 - (j + i)))
            {
            BVSRL_CONF1:
              /* check for non-recoverable conflict */
              if (btor->options.engine.val == BTOR_ENGINE_SLS
                  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
                return non_rec_conf (btor, bve, bvsrl, eidx, ">>");
#ifndef NDEBUG
              iscon = 1;
#endif
              // FIXME this should be random res <= clz_bvsrl
              // res = btor_uint64_to_bv (
              //    mm, (uint64_t) clz_bvsrl, sbw);
              shift = clz_bvsrl;
              BTOR_INC_REC_CONF_STATS (btor, 1);
              break;
            }
          }

          res = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
        }
      }
      else
      {
        goto BVSRL_CONF1;
      }

#if 0
	  for (i = 0, oneidx = -1; i < bvsrl->width; i++)
	    {
	      if (oneidx == -1 && btor_get_bit_bv (bve, bve->width - 1 - i))
		oneidx = i;
	      if (btor_get_bit_bv (bvsrl, bvsrl->width - 1 - i)) break;
	    }
	  shift = oneidx == -1 ? i : i - oneidx;
	  shiftconf = i;
#ifndef NDEBUG
	  for (i = 0; i < shift; i++)
	    assert (!btor_get_bit_bv (bvsrl, bvsrl->width - 1 - i));
#endif
	  // FIXME this is correct for clz(bve) > clz(t) by accident
	  // due to unsignedness of variable 'shift', because the case
	  // shift > bvsll->width - 1 captures this (-shift in unsigned
	  // is greater than bw)
	  // better to be more explicit
	  // clz(bve) = oneidx
	  // clz(t) = i
	  // rules:
	  //  -> clz(m) <= clz(t) then res = clz(t) - clz(m)
	  //  -> clz(m) > clz(t) then conflict
	  // FIXME FIXME FIXME
	  /* check for conflict -> do not allow shift by bw */
	  if (shift > bvsrl->width - 1)
	    {
	      /* check for non-recoverable conflict */
	      if (btor->options.engine.val == BTOR_ENGINE_SLS
		  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
		{
#ifndef NDEBUG
		  char *sbvsrl = btor_bv_to_char_bv (btor->mm, bvsrl);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := %s >> x", sbvsrl, sbve);
		  btor_freestr (btor->mm, sbvsrl);
		  btor_freestr (btor->mm, sbve);
#endif
		  BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
		  return 0;
		}
#ifndef NDEBUG
	      iscon = 1;
#endif
	      BTOR_INC_REC_CONF_STATS (btor, 1);
	      goto BVSRL_RANDOM_SHIFT;
	    }
	  /* x...x0 >> e[1] = 0...0 */
	  else if (btor_is_zero_bv (bvsrl))
	    {
	      bvmax = btor_ones_bv (btor->mm, sbw);
	      tmp = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
	      res = btor_new_random_range_bv (
		  btor->mm, &btor->rng, sbw, tmp, bvmax);
              btor_free_bv (btor->mm, bvmax);
              btor_free_bv (btor->mm, tmp);
	    }
	  else
	    {

	      /* check for conflict -> shifted bits must match */
	      for (i = 0, j = shift, res = 0; i < bve->width - j; i++)
		{
		  if (btor_get_bit_bv (bve, bve->width - 1 - i)
		      != btor_get_bit_bv (bvsrl, bvsrl->width - 1 - (j + i)))
		    {
		      /* check for non-recoverable conflict */
		      if (btor->options.engine.val == BTOR_ENGINE_SLS
			  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
			{
#ifndef NDEBUG
			  char *sbvsrl = btor_bv_to_char_bv (btor->mm, bvsrl);
			  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
			  BTORLOG (2, "prop CONFLICT: %s := %s >> x",
				   sbvsrl, sbve);
			  btor_freestr (btor->mm, sbvsrl);
			  btor_freestr (btor->mm, sbve);
#endif	      
			  BTOR_SLS_SOLVER (
			      btor)->stats.move_prop_non_rec_conf += 1;
			  return 0;
			}
#ifndef NDEBUG
		      iscon = 1;
#endif	      
		      res = btor_uint64_to_bv (mm, (uint64_t) shiftconf, sbw);
		      BTOR_INC_REC_CONF_STATS (btor, 1);
		      break;
		    }
		}

	      if (!res) res = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
	    }
#endif
    }
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
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
          return non_rec_conf (btor, bve, bvsrl, eidx, ">>");
#ifndef NDEBUG
        iscon = 1;
#endif
        BTOR_INC_REC_CONF_STATS (btor, 1);
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

    char *sbvsrl = btor_bv_to_char_bv (btor->mm, bvsrl);
    char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
    char *sres   = btor_bv_to_char_bv (btor->mm, res);
    if (eidx)
      BTORLOG (3,
               "prop (e[%d]): %s: %s := %s >> %s",
               eidx,
               node2string (srl),
               sbvsrl,
               eidx ? sbve : sres,
               eidx ? sres : sbve);
    btor_freestr (btor->mm, sbvsrl);
    btor_freestr (btor->mm, sbve);
    btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (mul);
  assert (BTOR_IS_REGULAR_NODE (mul));
  assert (bvmul);
  assert (bve);
  assert (bve->width == bvmul->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (mul->e[eidx])));

  int lsbve, lsbvmul, ispow2_bve;
  uint32_t i, j, bw;
  unsigned r;
  BtorBitVector *res, *inv, *tmp, *tmp2;
  BtorMemMgr *mm;
  BtorNode *e;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = mul->e[eidx ? 0 : 1];
  assert (e);
  bw = bvmul->width;

  res = 0;

  /* bve * res = bvmul
   *
   * -> if bve = 0: * bvmul = 0 -> choose random value for res
   *                * bvmul > 0 -> conflict
   *
   * -> if bvmul odd and bve even -> conflict
   *
   * -> if bve odd -> determine res via modular inverse (extended euklid)
   *		      (unique solution)
   *
   * -> else if bve is even (non-unique, multiple solutions possible!)
   *      * bve = 2^n: + if number of 0-LSBs in bvmul < n -> conflict
   *                   + else res = bvmul >> n
   *                     (with all bits shifted in randomly set to 0 or 1)
   *      * else: bve = 2^n * m, m is odd
   *		  + if number of 0-LSBs in bvmul < n -> conflict
   *	          + else c' = bvmul >> n
   *	            (with all bits shifted in randomly set to 0 or 1)
   *		    -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
   */

  lsbve   = btor_get_bit_bv (bve, 0);
  lsbvmul = btor_get_bit_bv (bvmul, 0);

  /* bve = 0 -> if bvmul = 0 choose random value, else conflict */
  if (btor_is_zero_bv (bve))
  {
    if (btor_is_zero_bv (bvmul))
    {
      res = btor_new_random_bv (mm, &btor->rng, bw);
    }
    else /* conflict */
    {
    BVMUL_CONF:
      /* check for non-recoverable conflict */
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = non_rec_conf (btor, bve, bvmul, eidx, "*");
      }
      else
      {
        /* bvmul odd -> do not choose even value for res
         * bvmul even -> choose either odd or even value for res */
        if (lsbvmul || btor_pick_rand_rng (&btor->rng, 0, 1))
        {
          /* res odd */
          res = btor_new_random_bv (mm, &btor->rng, bw);
          if (!btor_get_bit_bv (res, 0)) btor_set_bit_bv (res, 0, 1);
        }
        else
        {
          /* res even */
          r = btor_pick_rand_rng (&btor->rng, 0, 9);
          for (i = 0; i < bw; i++)
            if (btor_get_bit_bv (bvmul, i)) break;
          /* choose res as 2^n with prob 0.4 */
          if (r < 4)
          {
            res = btor_new_bv (mm, bw);
            btor_set_bit_bv (res, btor_pick_rand_rng (&btor->rng, 1, i), 1);
          }
          /* choose res as bvmul / 2^n with prob 0.4
           * (note: bw not necessarily power of 2 -> do not use srl) */
          else if (r < 8)
          {
            r   = btor_pick_rand_rng (&btor->rng, 1, i);
            tmp = btor_slice_bv (mm, bvmul, bw - 1, r);
            res = btor_uext_bv (mm, tmp, r);
            btor_free_bv (mm, tmp);
          }
          /* choose random even value with prob 0.2 */
          else
          {
            res = btor_new_random_bv (mm, &btor->rng, bw);
            if (btor_get_bit_bv (res, 0)) btor_set_bit_bv (res, 0, 0);
            btor_set_bit_bv (res, i, 1);
          }
        }
        BTOR_INC_REC_CONF_STATS (btor, 1);
      }
#ifndef NDEBUG
      iscon = 1;
#endif
    }
  }
  /* bvmul odd and bve even -> conflict */
  else if (lsbvmul && !lsbve)
  {
    goto BVMUL_CONF;
  }
  else
  {
    /* bve odd
     * -> determine res via modular inverse (extended euklid)
     *    (unique solution) */
    if (lsbve)
    {
      inv = btor_mod_inverse_bv (mm, bve);
      res = btor_mul_bv (mm, inv, bvmul);
      btor_free_bv (mm, inv);
    }
    /* bve even
     * (non-unique, multiple solutions possible!)
     * if bve = 2^n: + if number of 0-LSBs in bvmul < n -> conflict
     *               + else res = bvmul >> n
     *                      (with all bits shifted in set randomly)
     * else: bve = 2^n * m, m is odd
     *       + if number of 0-LSBs in bvmul < n -> conflict
     *       + else c' = bvmul >> n (with all bits shifted in set randomly)
     *	      res = c' * m^-1 (with m^-1 the mod inverse of m) */
    else
    {
      if ((ispow2_bve = btor_is_power_of_two_bv (bve)) >= 0)
      {
        for (i = 0; i < bw; i++)
          if (btor_get_bit_bv (bvmul, i)) break;
        /* number of 0-LSBs in bvmul < n (for bve = 2^n) -> conflict */
        if (i < (uint32_t) ispow2_bve)
        {
          goto BVMUL_CONF;
        }
        /* res = bvmul >> n with all bits shifted in set randomly
         * (note: bw is not necessarily power of 2 -> do not use srl) */
        else
        {
          tmp = btor_slice_bv (mm, bvmul, bw - 1, ispow2_bve);
          res = btor_uext_bv (mm, tmp, ispow2_bve);
          assert (res->width == bw);
          for (i = 0; i < (uint32_t) ispow2_bve; i++)
            btor_set_bit_bv (
                res, bw - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
          btor_free_bv (mm, tmp);
        }
      }
      else
      {
        for (i = 0; i < bw; i++)
          if (btor_get_bit_bv (bvmul, i)) break;
        for (j = 0; j < bw; j++)
          if (btor_get_bit_bv (bve, j)) break;
        /* number of 0-LSBs in bvmul < number of 0-SLBs in bve
         * -> conflict */
        if (i < j)
        {
          goto BVMUL_CONF;
        }
        /* c' = bvmul >> n (with all bits shifted in set randomly)
         * (note: bw is not necessarily power of 2 -> do not use srl)
         * -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd) */
        else
        {
          tmp = btor_slice_bv (mm, bvmul, bw - 1, j);
          res = btor_uext_bv (mm, tmp, j);
          assert (res->width == bw);
          btor_free_bv (mm, tmp);

          tmp  = btor_slice_bv (mm, bve, bw - 1, j);
          tmp2 = btor_uext_bv (mm, tmp, j);
          assert (tmp2->width == bw);
          assert (btor_get_bit_bv (tmp2, 0));
          inv = btor_mod_inverse_bv (mm, tmp2);
          btor_free_bv (mm, tmp);
          btor_free_bv (mm, tmp2);
          tmp = res;
          res = btor_mul_bv (mm, tmp, inv);
          /* choose one of all possible values */
          for (i = 0; i < j; i++)
            btor_set_bit_bv (
                res, bw - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
          btor_free_bv (mm, tmp);
          btor_free_bv (mm, inv);
        }
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

    char *sbvmul = btor_bv_to_char_bv (btor->mm, bvmul);
    char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
    char *sres   = btor_bv_to_char_bv (btor->mm, res);
    if (eidx)
      BTORLOG (3,
               "prop (e[%d]): %s: %s := %s * %s",
               eidx,
               node2string (mul),
               sbvmul,
               eidx ? sbve : sres,
               eidx ? sres : sbve);
    btor_freestr (btor->mm, sbvmul);
    btor_freestr (btor->mm, sbve);
    btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);
  assert (bve->width == bvudiv->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (udiv->e[eidx])));

  uint32_t bw;
  BtorNode *e;
  BtorBitVector *res, *lo, *up, *one, *bvmax, *tmp, *tmpbve;
  BtorMemMgr *mm;
  BtorRNG *rng;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm  = btor->mm;
  rng = &btor->rng;
  e   = udiv->e[eidx ? 0 : 1];
  assert (e);
  bw = bve->width;

  one   = btor_one_bv (mm, bve->width);
  bvmax = btor_ones_bv (mm, bvudiv->width); /* 2^bw - 1 */

  res = 0;

  /* bve / e[1] = bvudiv
   *
   * -> if bvudiv = 2^bw - 1: + bve = bvudiv = 2^bw - 1 -> e[1] = 1 or e[1] = 0
   *                          + bve != bvudiv -> e[1] = 0
   * -> if bvudiv = 0 and 0 < bve < 2^bw - 1 choose random e[1] > bve
   *                  and bve = 0            choose random e[1] > 0
   *                  else conflict
   * -> if bve < bvudiv -> conflict
   * -> if bvudiv is a divisor of bve choose with 0.5 prob out of
   *      + e[1] = bvudiv / bve
   *      + choose bve s.t. bve / e[1] = bvudiv
   * -> else choose bve s.t. bve / e[1] = bvudiv  */
  if (eidx)
  {
    if (!btor_compare_bv (bvudiv, bvmax))
    {
      /* bve = bvudiv = 2^bw - 1 -> choose either e[1] = 0 or e[1] = 1
       * with prob 0.5 */
      if (!btor_compare_bv (bve, bvudiv)
          && btor_pick_rand_rng (&btor->rng, 0, 1))
        res = btor_one_bv (mm, bw);
      /* bvudiv = 2^bw - 1 and bve != bvudiv -> e[1] = 0 */
      else
        res = btor_new_bv (mm, bw);
    }
    else if (btor_is_zero_bv (bvudiv))
    {
      /* bvudiv = 0 and bve = 0 -> choose random e[1] > 0 */
      if (btor_is_zero_bv (bve))
        res = btor_new_random_range_bv (mm, rng, bw, one, bvmax);
      /* bvudiv = 0 and 0 < bve < 2^bw - 1 -> choose random e[1] > bve */
      else if (btor_compare_bv (bve, bvmax))
      {
        tmp = btor_inc_bv (mm, bve);
        res = btor_new_random_range_bv (mm, rng, bw, tmp, bvmax);
        btor_free_bv (mm, tmp);
      }
      /* conflict */
      else
      {
      BVUDIV_E1_CONF:
        /* check for non-recoverable conflict */
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = non_rec_conf (btor, bve, bvudiv, eidx, "/");
        }
        /* disregard bve, choose e[1] s.t. e[1] * bvudiv does
         * not overflow */
        else
        {
          res = btor_new_random_range_bv (mm, rng, bw, one, bvmax);
          while (btor_is_umulo_bv (mm, res, bvudiv))
          {
            tmp = btor_sub_bv (mm, res, one);
            btor_free_bv (mm, res);
            res = btor_new_random_range_bv (mm, rng, bw, one, tmp);
            btor_free_bv (mm, tmp);
          }

          BTOR_INC_REC_CONF_STATS (btor, 1);
        }
#ifndef NDEBUG
        iscon = 1;
#endif
      }
    }
    else if (btor_compare_bv (bve, bvudiv) < 0)
    {
      /* bve < bvudiv -> conflict */
      goto BVUDIV_E1_CONF;
    }
    else
    {
      /* if bvudiv is a divisor of bve, choose e[1] = bve / bvudiv
       * with prob = 0.5 and a bve s.t. bve / e[1] = bvudiv otherwise */
      tmp = btor_urem_bv (mm, bve, bvudiv);
      if (btor_is_zero_bv (tmp) && btor_pick_rand_rng (rng, 0, 1))
      {
        btor_free_bv (mm, tmp);
        res = btor_udiv_bv (mm, bve, bvudiv);
      }
      else
      {
        /* choose e[1] out of all options that yield bve / e[1] = bvudiv
         * Note: udiv always truncates the results towards 0. */

        /* determine upper and lower bounds for e[1]:
         * up = bve / bvudiv
         * lo = bve / (bvudiv + 1) + 1
         * if lo > up -> conflict */
        btor_free_bv (mm, tmp);
        up  = btor_udiv_bv (mm, bve, bvudiv); /* upper bound */
        tmp = btor_inc_bv (mm, bvudiv);
        lo  = btor_udiv_bv (mm, bve, tmp); /* lower bound (excl.) */
        btor_free_bv (mm, tmp);
        tmp = lo;
        lo  = btor_inc_bv (mm, tmp); /* lower bound (incl.) */
        btor_free_bv (mm, tmp);

        /* lo > up -> conflict */
        if (btor_compare_bv (lo, up) > 0)
        {
          btor_free_bv (mm, lo);
          btor_free_bv (mm, up);
          goto BVUDIV_E1_CONF;
        }
        /* choose lo <= e[1] <= up */
        else
        {
          res = btor_new_random_range_bv (mm, rng, bw, lo, up);
          btor_free_bv (mm, lo);
          btor_free_bv (mm, up);
        }
      }
    }
  }

  /* e[0] / bve = bvudiv
   *
   * -> if bvudiv = 2^bw - 1 and bve = 1 e[0] = 2^bw-1
   *                         and bve = 0, choose random e[0] > 0
   *                         and bve > 0 -> conflict
   * -> if bve = 0 and bvudiv < 2^bw - 1 -> conflict
   * -> if bve * bvudiv does not overflow, choose with 0.5 prob out of
   *      + e[0] = bve * bvudiv
   *      + choose bve s.t. e[0] / bve = bvudiv
   * -> else choose bve s.t. e[0] / bve = bvudiv  */
  else
  {
    if (!btor_compare_bv (bvudiv, bvmax))
    {
      /* bvudiv = 2^bw-1 and bve = 1 -> e[0] = 2^bw-1 */
      if (!btor_compare_bv (bve, one)) res = btor_copy_bv (mm, bvmax);
      /* bvudiv = 2^bw - 1 and bve = 0 -> choose random e[0] */
      else if (btor_is_zero_bv (bve))
        res = btor_new_random_bv (mm, rng, bw);
      /* conflict */
      else
      {
      BVUDIV_E0_CONF:
        /* check for non-recoverable conflict */
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = non_rec_conf (btor, bve, bvudiv, eidx, "/");
        }
        /* disregard bve, choose bve s.t. e[0] = bve * bvudiv does
         * not overflow */
        else
        {
          tmpbve = btor_new_random_range_bv (mm, rng, bw, one, bvmax);
          while (btor_is_umulo_bv (mm, tmpbve, bvudiv))
          {
            tmp = btor_sub_bv (mm, tmpbve, one);
            btor_free_bv (mm, tmpbve);
            tmpbve = btor_new_random_range_bv (mm, rng, bw, one, tmp);
            btor_free_bv (mm, tmp);
          }
          res = btor_mul_bv (mm, tmpbve, bvudiv);
          btor_free_bv (mm, tmpbve);

          BTOR_INC_REC_CONF_STATS (btor, 1);
        }
#ifndef NDEBUG
        iscon = 1;
#endif
      }
    }
    else if (btor_is_zero_bv (bve))
    {
      /* bve = 0 and bvudiv < 2^bw - 1 -> conflict */
      goto BVUDIV_E0_CONF;
    }
    else
    {
      /* if bve * bvudiv does not overflow, choose e[0] = bve * bvudiv
       * with prob = 0.5 and a bve s.t. e[0] / bve = bvudiv otherwise */
      if (btor_is_umulo_bv (mm, bve, bvudiv))
        goto BVUDIV_E0_CONF;
      else
      {
        if (btor_pick_rand_rng (rng, 0, 1))
          res = btor_mul_bv (mm, bve, bvudiv);
        else
        {
          /* choose e[0] out of all options that yield
           * e[0] / bve = bvudiv
           * Note: udiv always truncates the results towards 0. */

          /* determine upper and lower bounds for e[0]:
           * up = bve * (budiv + 1) - 1
           *	  if bve * (bvudiv + 1) does not overflow
           *	  else 2^bw - 1
           * lo = bve * bvudiv */
          lo  = btor_mul_bv (mm, bve, bvudiv);
          tmp = btor_inc_bv (mm, bvudiv);
          if (btor_is_umulo_bv (mm, bve, tmp))
          {
            btor_free_bv (mm, tmp);
            up = btor_copy_bv (mm, bvmax);
          }
          else
          {
            up = btor_mul_bv (mm, bve, tmp);
            btor_free_bv (mm, tmp);
            tmp = btor_dec_bv (mm, up);
            btor_free_bv (mm, up);
            up = tmp;
          }

          res = btor_new_random_range_bv (mm, &btor->rng, bve->width, lo, up);

          btor_free_bv (mm, up);
          btor_free_bv (mm, lo);
        }
      }
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

    char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
    char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
    char *sres    = btor_bv_to_char_bv (btor->mm, res);
    if (eidx)
      BTORLOG (3,
               "prop (e[%d]): %s: %s := %s * %s",
               eidx,
               node2string (udiv),
               sbvudiv,
               eidx ? sbve : sres,
               eidx ? sres : sbve);
    btor_freestr (btor->mm, sbvudiv);
    btor_freestr (btor->mm, sbve);
    btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (urem);
  assert (BTOR_IS_REGULAR_NODE (urem));
  assert (bvurem);
  assert (bve);
  assert (bve->width == bvurem->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (urem->e[eidx])));

  uint32_t bw, cnt;
  int cmp;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp, *tmp2, *one, *n, *mul, *up, *sub;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e  = urem->e[eidx ? 0 : 1];
  assert (e);

  bw = bvurem->width;

  bvmax = btor_ones_bv (mm, bw); /* 2^bw - 1 */
  one   = btor_one_bv (mm, bw);

  res = 0;

  /* bve % e[1] = bvurem
   * -> if bvurem = 1...1 -> bve = 1...1 and e[1] = 0...0, else conflict
   * -> if bve = bvurem, choose either e[1] = 0 or some e[1] > bvurem randomly
   * -> if bvurem > 0 and bvurem = bve - 1, conflict
   * -> if bve > bvurem, e[1] = ((bve - bvurem) / n) > bvurem, else conflict
   * -> if bve < bvurem, conflict */
  if (eidx)
  {
    /* bve % e[1] = 1...1 -> bve = 1...1, e[1] = 0 */
    if (!btor_compare_bv (bvurem, bvmax))
    {
      /* conflict */
      if (btor_compare_bv (bve, bvmax))
      {
#ifndef NDEBUG
        iscon = 1;
#endif
        /* check for non-recoverable conflict */
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = non_rec_conf (btor, bve, bvurem, eidx, "%");
        }
        else
        {
          res = btor_new_bv (mm, bw);
          BTOR_INC_REC_CONF_STATS (btor, 1);
        }
      }
      else
      {
        res = btor_new_bv (mm, bw);
      }
    }
    else
    {
      cmp = btor_compare_bv (bve, bvurem);

      /* bve = bvurem, choose either e[1] = 0 or random e[1] > bvurem */
      if (cmp == 0)
      {
      BVUREM_EQ_1:
        /* choose e[1] = 0 with prob = 0.25*/
        if (!btor_pick_rand_rng (&btor->rng, 0, 3)) res = btor_new_bv (mm, bw);
        /* bvurem < res <= 2^bw - 1 */
        else
        {
          tmp = btor_add_bv (mm, bvurem, one);
          res = btor_new_random_range_bv (mm, &btor->rng, bw, tmp, bvmax);
          btor_free_bv (mm, tmp);
        }
      }
      /* bve > bvurem, e[1] = (bve - bvurem) / n */
      else if (cmp > 0)
      {
        if (!btor_is_zero_bv (bvurem))
        {
          tmp = btor_dec_bv (mm, bve);
          /* bvurem = bve - 1 -> bve % e[1] = bve - 1
           * -> not possible if bvurem > 0 -> conflict */
          if (!btor_compare_bv (bvurem, tmp))
          {
            btor_free_bv (mm, tmp);
            goto BVUREM_CONF_1;
          }
          btor_free_bv (mm, tmp);
        }

        sub = btor_sub_bv (mm, bve, bvurem);

        /* bve - bvurem <= bvurem -> conflict */
        if (btor_compare_bv (sub, bvurem) <= 0)
        {
          btor_free_bv (mm, sub);
          goto BVUREM_CONF_1;
        }
        /* choose either n = 1 or 1 <= n < (bve - bvurem) / bvurem
         * with prob = 0.5 */
        else
        {
          if (!btor_pick_rand_rng (&btor->rng, 0, 1))
          {
            res = btor_copy_bv (mm, sub);
          }
          else
          {
            /* 1 <= n < (bve - bvurem) / bvurem (non-truncating)
             * (note: div truncates towards 0!) */

            /* bvurem = 0 -> 1 <= n <= bve */
            if (btor_is_zero_bv (bvurem))
            {
              up = btor_copy_bv (mm, bve);
            }
            /* e[1] > bvurem
             * -> (bve - bvurem) / n > bvurem
             * -> (bve - bvurem) / bvurem > n */
            else
            {
              tmp  = btor_urem_bv (mm, sub, bvurem);
              tmp2 = btor_udiv_bv (mm, sub, bvurem);
              if (btor_is_zero_bv (tmp))
              {
                /* (bve - bvurem) / bvurem is not truncated
                 * (remainder is 0), therefore the EXclusive
                 * upper bound
                 * -> up = (bve - bvurem) / bvurem - 1 */
                up = btor_sub_bv (mm, tmp2, one);
                btor_free_bv (mm, tmp2);
              }
              else
              {
                /* (bve - bvurem) / bvurem is truncated
                 * (remainder is not 0), therefore the INclusive
                 * upper bound
                 * -> up = (bve - bvurem) / bvurem */
                up = tmp2;
              }
              btor_free_bv (mm, tmp);
            }

            if (btor_is_zero_bv (up))
              res = btor_udiv_bv (mm, sub, one);
            else
            {
              /* choose 1 <= n <= up randomly
               * s.t (bve - bvurem) % n = 0 */
              n   = btor_new_random_range_bv (mm, &btor->rng, bw, one, up);
              tmp = btor_urem_bv (mm, sub, n);
              for (cnt = 0; cnt < bw && !btor_is_zero_bv (tmp); cnt++)
              {
                btor_free_bv (mm, n);
                btor_free_bv (mm, tmp);
                n   = btor_new_random_range_bv (mm, &btor->rng, bw, one, up);
                tmp = btor_urem_bv (mm, sub, n);
              }

              /* res = (bve - bvurem) / n */
              if (btor_is_zero_bv (tmp)) res = btor_udiv_bv (mm, sub, n);
              /* fallback: n = 1 */
              else
                res = btor_copy_bv (mm, sub);

              btor_free_bv (mm, n);
              btor_free_bv (mm, tmp);
            }
            btor_free_bv (mm, up);
          }
        }
        btor_free_bv (mm, sub);
      }
      /* bve < bvurem (conflict) */
      else
      {
      BVUREM_CONF_1:
        /* check for non-recoverable conflict */
#ifndef NDEBUG
        iscon = 1;
#endif
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = non_rec_conf (btor, bve, bvurem, eidx, "%");
        }
        else
        {
          BTOR_INC_REC_CONF_STATS (btor, 1);

          /* choose simplest solution with prob 0.5 */
          if (btor_pick_rand_rng (&btor->rng, 0, 1)) goto BVUREM_EQ_1;
          /* choose random value > bvurem */
          else
          {
            tmp = btor_add_bv (mm, bvurem, one);
            res = btor_new_random_range_bv (mm, &btor->rng, bw, tmp, bvmax);
            btor_free_bv (mm, tmp);
          }
        }
      }
    }
  }
  /* e[0] % bve = bvurem
   * -> if bve = 0, e[0] = bvurem
   * -> if bvurem = 1...1 and bve != 0, conflict
   * -> if bve <= bvurem, conflict
   * -> if bvurem > 0 and bve = 1, conflict
   * -> else choose either
   *      - e[0] = bvurem, or
   *      - e[0] = bve * n + b, with n s.t. (bve * n + b) does not overflow */
  else
  {
    /* bve = 0 -> e[0] = bvurem */
    if (btor_is_zero_bv (bve))
    {
    BVUREM_ZERO_0:
      res = btor_copy_bv (btor->mm, bvurem);
    }
    /* bvurem > 0 and bve = 1, conflict */
    else if (!btor_is_zero_bv (bvurem) && btor_is_one_bv (bve))
      goto BVUREM_CONF_0;
    /* bvurem = 1...1 -> bve = 0, e[0] = 1...1 */
    else if (!btor_compare_bv (bvurem, bvmax))
    {
      /* conflict (bve != 0) */
      if (!btor_is_zero_bv (bve))
      {
#ifndef NDEBUG
        iscon = 1;
#endif
        /* check for non-recoverable conflict */
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = non_rec_conf (btor, bve, bvurem, eidx, "%");
        }
        else
        {
          BTOR_INC_REC_CONF_STATS (btor, 1);
          goto BVUREM_ZERO_0;
        }
      }
      else
      {
        goto BVUREM_ZERO_0;
      }
    }
    else if (btor_compare_bv (bve, bvurem) > 0)
    {
      /* choose simplest solution (0 <= res < bve -> res = bvurem)
       * with prob 0.5 */
      if (btor_pick_rand_rng (&btor->rng, 0, 1))
      {
      BVUREM_EQ_0:
        res = btor_copy_bv (mm, bvurem);
      }
      /* e[0] = bve * n + bvurem,
       * with n s.t. (bve * n + bvurem) does not overflow */
      else
      {
        tmp2 = btor_sub_bv (mm, bvmax, bve);

        /* overflow for n = 1 -> only simplest solution possible */
        if (btor_compare_bv (tmp2, bvurem) < 0)
        {
          btor_free_bv (mm, tmp2);
          goto BVUREM_EQ_0;
        }
        else
        {
          btor_free_bv (mm, tmp2);

          tmp = btor_copy_bv (mm, bvmax);
          n   = btor_new_random_range_bv (mm, &btor->rng, bw, one, tmp);

          while (btor_is_umulo_bv (mm, bve, n))
          {
            btor_free_bv (mm, tmp);
            tmp = btor_sub_bv (mm, n, one);
            btor_free_bv (mm, n);
            n = btor_new_random_range_bv (mm, &btor->rng, bw, one, tmp);
          }

          mul  = btor_mul_bv (mm, bve, n);
          tmp2 = btor_sub_bv (mm, bvmax, mul);

          if (btor_compare_bv (tmp2, bvurem) < 0)
          {
            btor_free_bv (mm, tmp);
            tmp = btor_sub_bv (mm, n, one);
            btor_free_bv (mm, n);
            n = btor_new_random_range_bv (mm, &btor->rng, bw, one, tmp);
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
    BVUREM_CONF_0:
      /* check for non-recoverable conflict */
#ifndef NDEBUG
      iscon = 1;
#endif
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = non_rec_conf (btor, bve, bvurem, eidx, "%");
      }
      else
      {
        BTOR_INC_REC_CONF_STATS (btor, 1);
        /* choose simplest solution with prob 0.5 */
        if (btor_pick_rand_rng (&btor->rng, 0, 1)) goto BVUREM_EQ_0;
        /* choose random value > bvurem */
        else
        {
          tmp = btor_add_bv (mm, bvurem, one);
          res = btor_new_random_range_bv (mm, &btor->rng, bw, tmp, bvmax);
          btor_free_bv (mm, tmp);
        }
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

    char *sbvurem = btor_bv_to_char_bv (btor->mm, bvurem);
    char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
    char *sres    = btor_bv_to_char_bv (btor->mm, res);
    if (eidx)
      BTORLOG (3,
               "prop (e[%d]): %s: %s := %s %% %s",
               eidx,
               node2string (urem),
               sbvurem,
               eidx ? sbve : sres,
               eidx ? sres : sbve);
    btor_freestr (btor->mm, sbvurem);
    btor_freestr (btor->mm, sbve);
    btor_freestr (btor->mm, sres);
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
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
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

  res = 0;

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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = non_rec_conf (btor, bve, bvconcat, eidx, "o");
      }
      else
      {
        BTOR_INC_REC_CONF_STATS (btor, 1);
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = non_rec_conf (btor, bve, bvconcat, eidx, "o");
      }
      else
      {
        BTOR_INC_REC_CONF_STATS (btor, 1);
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

    char *sbvconcat = btor_bv_to_char_bv (btor->mm, bvconcat);
    char *sbve      = btor_bv_to_char_bv (btor->mm, bve);
    char *sres      = btor_bv_to_char_bv (btor->mm, res);
    if (eidx)
      BTORLOG (3,
               "prop (e[%d]): %s: %s := %s o %s",
               eidx,
               node2string (concat),
               sbvconcat,
               eidx ? sbve : sres,
               eidx ? sres : sbve);
    btor_freestr (btor->mm, sbvconcat);
    btor_freestr (btor->mm, sbve);
    btor_freestr (btor->mm, sres);
  }
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_slice_bv (Btor *btor,
              BtorNode *slice,
              BtorBitVector *bvslice,
              BtorBitVector *bve)
{
  assert (btor);
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (slice);
  assert (BTOR_IS_REGULAR_NODE (slice));
  assert (bvslice);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (slice->e[0])));

  uint32_t i, r, upper, lower;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
#endif

  mm = btor->mm;
  e  = slice->e[0];
  assert (e);

  r = btor_pick_rand_rng (&btor->rng, 0, 1);

  upper = btor_slice_get_upper (slice);
  lower = btor_slice_get_lower (slice);

  res = btor_new_bv (mm, btor_get_exp_width (btor, e));
  /* keep previous value for don't care bits or set randomly with prob = 0.5 */
  for (i = 0; i < lower; i++)
    btor_set_bit_bv (res,
                     i,
                     r ? btor_get_bit_bv (bve, i)
                       : (int) btor_pick_rand_rng (&btor->rng, 0, 1));
  /* set sliced bits to propagated value */
  for (i = lower; i <= upper; i++)
    btor_set_bit_bv (res, i, btor_get_bit_bv (bvslice, i - lower));
  /* keep previous value for don't care bits or set randomly with prob = 0.5 */
  for (i = upper + 1; i < res->width; i++)
    btor_set_bit_bv (res,
                     i,
                     r ? btor_get_bit_bv (bve, i)
                       : (int) btor_pick_rand_rng (&btor->rng, 0, 1));

#ifndef NDEBUG
  tmpdbg = btor_slice_bv (mm, res, upper, lower);
  assert (!btor_compare_bv (tmpdbg, bvslice));
  btor_free_bv (mm, tmpdbg);

  char *sbvslice = btor_bv_to_char_bv (btor->mm, bvslice);
  char *sres     = btor_bv_to_char_bv (btor->mm, res);
  BTORLOG (3,
           "prop (xxxxx): %s: %s := %s[%d:%d]",
           node2string (slice),
           sbvslice,
           sres,
           lower,
           upper);
  btor_freestr (btor->mm, sbvslice);
  btor_freestr (btor->mm, sres);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

static inline BtorBitVector *
cons_add_bv (Btor *btor,
             BtorNode *add,
             BtorBitVector *bvadd,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (add);
  assert (BTOR_IS_REGULAR_NODE (add));
  assert (bvadd);
  assert (bve);
  assert (bve->width == bvadd->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (add->e[eidx])));

  (void) add;
  (void) bve;
  (void) eidx;

  return btor_new_random_bv (btor->mm, &btor->rng, bvadd->width);
}

static inline BtorBitVector *
cons_and_bv (Btor *btor,
             BtorNode *and,
             BtorBitVector *bvand,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (and);
  assert (BTOR_IS_REGULAR_NODE (and));
  assert (bvand);
  assert (bve);
  assert (bve->width == bvand->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (and->e[eidx])));

  uint32_t i;
  BtorBitVector *res;

  (void) and;
  (void) bve;
  (void) eidx;

  res = btor_new_bv (btor->mm, bvand->width);

  /* bve & res = bvand
   * -> all bits set in bvand must be set in res
   * -> all bits not set in bvand are chosen to be set randomly */
  for (i = 0; i < bvand->width; i++)
  {
    if (btor_get_bit_bv (bvand, i))
      btor_set_bit_bv (res, i, 1);
    else
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }

  return res;
}

static inline BtorBitVector *
cons_eq_bv (
    Btor *btor, BtorNode *eq, BtorBitVector *bveq, BtorBitVector *bve, int eidx)
{
  assert (btor);
  assert (eq);
  assert (BTOR_IS_REGULAR_NODE (eq));
  assert (bveq);
  assert (bveq->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (eq->e[eidx])));

  (void) eq;
  (void) bveq;
  (void) bve;
  (void) eidx;

  return btor_new_random_bv (btor->mm, &btor->rng, bve->width);
}

static inline BtorBitVector *
cons_ult_bv (Btor *btor,
             BtorNode *ult,
             BtorBitVector *bvult,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (ult);
  assert (BTOR_IS_REGULAR_NODE (ult));
  assert (bvult);
  assert (bvult->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (ult->e[eidx])));

  bool isult;
  uint32_t bw;
  BtorBitVector *bvmax, *zero, *tmp, *res;

  (void) ult;

  bw    = bve->width;
  isult = !btor_is_zero_bv (bvult);
  zero  = btor_new_bv (btor->mm, bw);
  bvmax = btor_ones_bv (btor->mm, bw);

  if (eidx && isult)
  {
    /* bve < res = 1  ->  res > 0 */
    tmp = btor_one_bv (btor->mm, bw);
    res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, tmp, bvmax);
    btor_free_bv (btor->mm, tmp);
  }
  else if (!eidx && isult)
  {
    /* res < bve = 1  ->  0 <= res < 1...1 */
    tmp = btor_dec_bv (btor->mm, bvmax);
    res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, zero, tmp);
    btor_free_bv (btor->mm, tmp);
  }
  else
  {
    res = btor_new_random_bv (btor->mm, &btor->rng, bw);
  }

  btor_free_bv (btor->mm, bvmax);
  btor_free_bv (btor->mm, zero);

  return res;
}

static inline BtorBitVector *
cons_sll_bv (Btor *btor,
             BtorNode *sll,
             BtorBitVector *bvsll,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (sll);
  assert (BTOR_IS_REGULAR_NODE (sll));
  assert (bvsll);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsll->width);
  assert (eidx || btor_log_2_util (bvsll->width) == bve->width);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (sll->e[eidx])));

  uint32_t i, s, bw, sbw;
  BtorBitVector *res, *from, *to, *shift;

  (void) sll;
  (void) bve;

  bw  = bvsll->width;
  sbw = btor_log_2_util (bw);

  for (i = 0; i < bw; i++)
    if (btor_get_bit_bv (bvsll, i)) break;

  from  = btor_new_bv (btor->mm, sbw);
  to    = btor_uint64_to_bv (btor->mm, i == bw ? i - 1 : i, sbw);
  shift = btor_new_random_range_bv (btor->mm, &btor->rng, sbw, from, to);
  btor_free_bv (btor->mm, from);
  btor_free_bv (btor->mm, to);

  if (eidx)
  {
    res = shift;
  }
  else
  {
    s   = btor_bv_to_uint64_bv (shift);
    res = btor_srl_bv (btor->mm, bvsll, shift);
    for (i = 0; i < s; i++)
      btor_set_bit_bv (res, bw - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
    btor_free_bv (btor->mm, shift);
  }

  return res;
}

static inline BtorBitVector *
cons_srl_bv (Btor *btor,
             BtorNode *srl,
             BtorBitVector *bvsrl,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (srl);
  assert (BTOR_IS_REGULAR_NODE (srl));
  assert (bvsrl);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsrl->width);
  assert (eidx || btor_log_2_util (bvsrl->width) == bve->width);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (srl->e[eidx])));

  uint32_t i, s, bw, sbw;
  BtorBitVector *res, *from, *to, *shift;

  (void) srl;
  (void) bve;

  bw  = bvsrl->width;
  sbw = btor_log_2_util (bw);

  for (i = 0; i < bw; i++)
    if (btor_get_bit_bv (bvsrl, bw - 1 - i)) break;

  from  = btor_new_bv (btor->mm, sbw);
  to    = btor_uint64_to_bv (btor->mm, i == bw ? i - 1 : i, sbw);
  shift = btor_new_random_range_bv (btor->mm, &btor->rng, sbw, from, to);
  btor_free_bv (btor->mm, from);
  btor_free_bv (btor->mm, to);

  if (eidx)
  {
    res = shift;
  }
  else
  {
    s   = btor_bv_to_uint64_bv (shift);
    res = btor_srl_bv (btor->mm, bvsrl, shift);
    for (i = 0; i < s; i++)
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
    btor_free_bv (btor->mm, shift);
  }

  return res;
}

static inline BtorBitVector *
cons_mul_bv (Btor *btor,
             BtorNode *mul,
             BtorBitVector *bvmul,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (mul);
  assert (BTOR_IS_REGULAR_NODE (mul));
  assert (bvmul);
  assert (bve);
  assert (bve->width == bvmul->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (mul->e[eidx])));

  uint32_t i, j, bw;
  BtorBitVector *res, *zero, *bvmax;

  (void) mul;
  (void) bve;
  (void) eidx;

  bw  = bvmul->width;
  res = btor_new_random_bv (btor->mm, &btor->rng, bw);
  if (!btor_is_zero_bv (bvmul))
  {
    if (btor_is_zero_bv (res))
    {
      zero  = res;
      bvmax = btor_ones_bv (btor->mm, bw);
      res   = btor_new_random_range_bv (btor->mm, &btor->rng, bw, zero, bvmax);
      btor_free_bv (btor->mm, zero);
      btor_free_bv (btor->mm, bvmax);
    }
    /* bvmul odd -> choose odd value > 0 */
    if (btor_get_bit_bv (bvmul, 0))
    {
      if (!btor_get_bit_bv (res, 0)) btor_set_bit_bv (res, 0, 1);
    }
    /* bvmul even -> choose random value > 0
     *               with number of 0-LSBs in res less or equal
     *               than in bvmul */
    else
    {
      for (i = 0; i < bw; i++)
        if (btor_get_bit_bv (bvmul, bw - 1 - i)) break;
      for (j = 0; j < bw; j++)
        if (btor_get_bit_bv (res, bw - 1 - j)) break;
      if (j > i)
        btor_set_bit_bv (res, btor_pick_rand_rng (&btor->rng, 0, i), 1);
    }
  }

  return res;
}

static inline BtorBitVector *
cons_udiv_bv (Btor *btor,
              BtorNode *udiv,
              BtorBitVector *bvudiv,
              BtorBitVector *bve,
              int eidx)
{
  assert (btor);
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);
  assert (bve->width == bvudiv->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (udiv->e[eidx])));

  uint32_t bw;
  BtorBitVector *res, *tmp, *tmpbve, *zero, *one, *bvmax;

  bw    = bvudiv->width;
  zero  = btor_new_bv (btor->mm, bw);
  one   = btor_one_bv (btor->mm, bw);
  bvmax = btor_ones_bv (btor->mm, bw);

  (void) udiv;
  (void) bve;

  if (eidx)
  {
    /* -> bvudiv = 1...1 then res = 0 or res = 1
     * -> else choose res s.t. res * bvudiv does not overflow */
    if (!btor_compare_bv (bvudiv, bvmax))
      res = btor_uint64_to_bv (
          btor->mm, btor_pick_rand_rng (&btor->rng, 0, 1), bw);
    else
    {
      res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, one, bvmax);
      while (btor_is_umulo_bv (btor->mm, res, bvudiv))
      {
        tmp = btor_sub_bv (btor->mm, res, one);
        btor_free_bv (btor->mm, res);
        res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, one, tmp);
        btor_free_bv (btor->mm, tmp);
      }
    }
  }
  else
  {
    /* -> bvudiv = 0 then res < 1...1
     * -> bvudiv = 1...1 then choose random res
     * -> else choose tmpbve s.t. res = tmpbve * bvudiv does not overflow */
    if (btor_is_zero_bv (bvudiv))
    {
      tmp = btor_dec_bv (btor->mm, bvmax);
      res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, zero, tmp);
      btor_free_bv (btor->mm, tmp);
    }
    else if (!btor_compare_bv (bvudiv, bvmax))
    {
      res = btor_new_random_bv (btor->mm, &btor->rng, bw);
    }
    else
    {
      tmpbve = btor_new_random_range_bv (btor->mm, &btor->rng, bw, one, bvmax);
      while (btor_is_umulo_bv (btor->mm, tmpbve, bvudiv))
      {
        tmp = btor_sub_bv (btor->mm, tmpbve, one);
        btor_free_bv (btor->mm, tmpbve);
        tmpbve = btor_new_random_range_bv (btor->mm, &btor->rng, bw, one, tmp);
        btor_free_bv (btor->mm, tmp);
      }
      res = btor_mul_bv (btor->mm, tmpbve, bvudiv);
      btor_free_bv (btor->mm, tmpbve);
    }
  }

  btor_free_bv (btor->mm, one);
  btor_free_bv (btor->mm, bvmax);
  return res;
}

static inline BtorBitVector *
cons_urem_bv (Btor *btor,
              BtorNode *urem,
              BtorBitVector *bvurem,
              BtorBitVector *bve,
              int eidx)
{
  assert (btor);
  assert (urem);
  assert (BTOR_IS_REGULAR_NODE (urem));
  assert (bvurem);
  assert (bve);
  assert (bve->width == bvurem->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (urem->e[eidx])));

  uint32_t bw;
  BtorBitVector *res, *bvmax, *tmp;

  (void) urem;
  (void) bve;

  bw    = bvurem->width;
  bvmax = btor_ones_bv (btor->mm, bw);

  if (eidx)
  {
    /* bvurem = 1...1  ->  res = 0 */
    if (!btor_compare_bv (bvurem, bvmax))
    {
      res = btor_new_bv (btor->mm, bw);
    }
    /* else res > bvurem */
    else
    {
      tmp = btor_inc_bv (btor->mm, bvurem);
      res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, tmp, bvmax);
      btor_free_bv (btor->mm, tmp);
    }
  }
  else
  {
    /* bvurem = 1...1  ->  res = 1...1 */
    if (!btor_compare_bv (bvurem, bvmax))
    {
      res = btor_copy_bv (btor->mm, bvmax);
    }
    /* else res >= bvurem */
    else
    {
      res = btor_new_random_range_bv (btor->mm, &btor->rng, bw, bvurem, bvmax);
    }
  }

  btor_free_bv (btor->mm, bvmax);
  return res;
}

static inline BtorBitVector *
cons_concat_bv (Btor *btor,
                BtorNode *concat,
                BtorBitVector *bvconcat,
                BtorBitVector *bve,
                int eidx)
{
  assert (btor);
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (concat);
  assert (BTOR_IS_REGULAR_NODE (concat));
  assert (bvconcat);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (concat->e[eidx])));

  (void) concat;

  if (eidx)
    return btor_slice_bv (
        btor->mm, bvconcat, bvconcat->width - bve->width - 1, 0);
  else
    return btor_slice_bv (btor->mm, bvconcat, bvconcat->width - 1, bve->width);
}

static inline BtorBitVector *
cons_slice_bv (Btor *btor,
               BtorNode *slice,
               BtorBitVector *bvslice,
               BtorBitVector *bve)
{
  return inv_slice_bv (btor, slice, bvslice, bve);
}

/*------------------------------------------------------------------------*/

void
btor_select_move_prop (Btor *btor,
                       BtorNode *root,
                       BtorNode **input,
                       BtorBitVector **assignment)
{
  assert (btor);
  assert (btor_check_id_table_mark_unset_dbg (btor));
  assert (root);
  assert (
      btor_bv_to_uint64_bv ((BtorBitVector *) btor_get_bv_model (btor, root))
      == 0);

  int i, nconst, eidx, idx;
  uint32_t r, p;
  BtorNode *cur, *real_cur;
  BtorBitVector *bve[3], *bvcur, *bvenew, *tmp;

  *input      = 0;
  *assignment = 0;

  cur   = root;
  bvcur = btor_one_bv (btor->mm, 1);

  if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (cur)))
  {
    *input      = BTOR_REAL_ADDR_NODE (cur);
    *assignment = BTOR_IS_INVERTED_NODE (cur) ? btor_not_bv (btor->mm, bvcur)
                                              : btor_copy_bv (btor->mm, bvcur);
  }
  else
  {
    p = btor->options.prop_use_inv_value.val;

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

      /* conflict */
      for (i = 0, nconst = 0; i < real_cur->arity; i++)
      {
        bve[i] = (BtorBitVector *) btor_get_bv_model (btor, real_cur->e[i]);
        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[i])))
          nconst += 1;
      }
      if (nconst > real_cur->arity - 1) break;

#ifndef NDEBUG
      char *a = btor_bv_to_char_bv (btor->mm, bvcur);
      BTORLOG (2, "");
      BTORLOG (2, "propagate: %s", a);
      btor_freestr (btor->mm, a);
#endif
      /* we either select a consistent or inverse value
       * as path assignment, depending on the given probability p
       * -> if r < p then inverse else consistent */
      r = btor_pick_rand_rng (&btor->rng,
                              btor->options.prop_use_inv_value.min,
                              btor->options.prop_use_inv_value.max - 1);

      /* select path and determine path assignment */
      switch (real_cur->kind)
      {
        case BTOR_ADD_NODE:
          eidx = select_path_add (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_add_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_add_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_AND_NODE:
          eidx = select_path_and (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_and_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_and_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_BEQ_NODE:
          eidx = select_path_eq (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_eq_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_eq_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_ULT_NODE:
          eidx = select_path_ult (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_ult_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_ult_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_SLL_NODE:
          eidx = select_path_sll (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_sll_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_sll_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_SRL_NODE:
          eidx = select_path_srl (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_srl_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_srl_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_MUL_NODE:
          eidx = select_path_mul (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_mul_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_mul_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_UDIV_NODE:
          eidx = select_path_udiv (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_udiv_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_udiv_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_UREM_NODE:
          eidx = select_path_urem (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p ? inv_urem_bv (btor, real_cur, bvcur, bve[idx], eidx)
                         : cons_urem_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_CONCAT_NODE:
          eidx = select_path_concat (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = r < p
                       ? inv_concat_bv (btor, real_cur, bvcur, bve[idx], eidx)
                       : cons_concat_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        default:
          assert (real_cur->kind == BTOR_SLICE_NODE);
          eidx = select_path_slice (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0),
              bvenew = inv_slice_bv (btor, real_cur, bvcur, bve[0]);
      }

      if (!bvenew) break; /* non-recoverable conflict */

      cur = real_cur->e[eidx];

      /* found input and assignment */
      if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[eidx])))
      {
      FOUND_RESULT:
        *input      = BTOR_REAL_ADDR_NODE (cur);
        *assignment = BTOR_IS_INVERTED_NODE (cur)
                          ? btor_not_bv (btor->mm, bvenew)
                          : btor_copy_bv (btor->mm, bvenew);
        btor_free_bv (btor->mm, bvenew);
        break;
      }
      else if (BTOR_IS_BV_COND_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[eidx])))
      {
        real_cur = BTOR_REAL_ADDR_NODE (cur);
        do
        {
          /* either assume that cond is fixed and propagate bvenew
           * to enabled path, or flip condition */
          tmp = (BtorBitVector *) btor_get_bv_model (btor, real_cur->e[0]);
          // TODO RENAME OPTIONS
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

          real_cur = BTOR_REAL_ADDR_NODE (cur);
        } while (BTOR_IS_BV_COND_NODE (real_cur));

        if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (cur)))
        {
          goto FOUND_RESULT;
        }
        else if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cur)))
        {
          /* if input is const -> conflict */
          btor_free_bv (btor->mm, bvenew);
          break;
        }
      }

      btor_free_bv (btor->mm, bvcur);
      bvcur = bvenew;
    }
  }
  btor_free_bv (btor->mm, bvcur);
}

/*------------------------------------------------------------------------*/

static void
reset_cone (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor_check_id_table_mark_unset_dbg (btor));
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorNode *cur;
  BtorNodeIterator nit;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, unmark_stack;
  BtorPropSolver *slv;

  bv_model = btor->bv_model;
  assert (bv_model);
  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  score = slv->score;
  assert (!btor->options.prop_use_bandit.val || score);

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  BTOR_PUSH_STACK (btor->mm, stack, exp);
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
    if (btor->options.prop_use_bandit.val)
    {
      if ((b = btor_get_ptr_hash_table (score, cur)))
        btor_remove_ptr_hash_table (score, cur, 0, 0);
      if ((b = btor_get_ptr_hash_table (score, BTOR_INVERT_NODE (cur))))
        btor_remove_ptr_hash_table (score, BTOR_INVERT_NODE (cur), 0, 0);
    }

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
update_cone (Btor *btor, BtorNode *exp, BtorBitVector *assignment)
{
  assert (btor);
  assert (BTOR_PROP_SOLVER (btor));
  assert (exp);

  reset_cone (btor, exp);
  btor_add_to_bv_model (btor, btor->bv_model, exp, assignment);
  btor_generate_model (btor, btor->bv_model, btor->fun_model, 0);
  if (btor->options.prop_use_bandit.val)
    btor_compute_sls_scores (btor, BTOR_PROP_SOLVER (btor)->score);
}

static BtorNode *
select_constraint (Btor *btor, uint32_t nmoves)
{
  assert (btor);

  BtorNode *res, *cur;
  BtorPropSolver *slv;
  BtorHashTableIterator it;

  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  assert (slv->roots);

  if (btor->options.prop_use_bandit.val)
  {
    assert (slv->score);

    int *selected;
    double value, max_value, score;
    BtorPtrHashBucket *b;

    res       = 0;
    max_value = 0.0;
    btor_init_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      selected = &it.bucket->data.as_int;
      cur      = btor_next_node_hash_table_iterator (&it);
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cur))
          && btor_is_zero_bv (btor_get_bv_model (btor, cur)))
        return 0; /* contains false constraint -> unsat */
      b = btor_get_ptr_hash_table (slv->score, cur);
      assert (b);
      if ((score = b->data.as_dbl) >= 1.0) continue;
      if (!res)
      {
        res = cur;
        *selected += 1;
        continue;
      }

      value = score + BTOR_PROP_SELECT_CFACT * sqrt (log (*selected) / nmoves);
      if (value > max_value)
      {
        res       = cur;
        max_value = value;
        *selected += 1;
      }
    }
  }
  else
  {
    uint32_t r;
    BtorNodePtrStack stack;

    res = 0;
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
      if (!btor_is_zero_bv (btor_get_bv_model (btor, cur))) continue;
      BTOR_PUSH_STACK (btor->mm, stack, cur);
    }
    assert (BTOR_COUNT_STACK (stack));
    r   = btor_pick_rand_rng (&btor->rng, 0, BTOR_COUNT_STACK (stack) - 1);
    res = stack.start[r];
    BTOR_RELEASE_STACK (btor->mm, stack);
  }

  assert (res);

  BTORLOG (1, "");
  BTORLOG (1, "select constraint: %s", node2string (res));

  return res;
}

static inline bool
all_constraints_sat (Btor *btor)
{
  assert (btor);

  bool res;
  BtorNode *root;
  BtorHashTableIterator it;

  res = true;
  btor_init_node_hash_table_iterator (&it, BTOR_PROP_SOLVER (btor)->roots);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    if (btor_is_zero_bv (btor_get_bv_model (btor, root)))
    {
      res = false;
      break;
    }
  }
  return res;
}

static int
move (Btor *btor, uint32_t nmoves)
{
  assert (btor);
  assert (!all_constraints_sat (btor));

  BTORLOG (1, "");
  BTORLOG (1, "*** move");

  BtorNode *root, *input;
  BtorBitVector *assignment;

  /* roots contain false constraint -> unsat */
  if (!(root = select_constraint (btor, nmoves))) return 0;

  do
  {
    btor_select_move_prop (btor, root, &input, &assignment);
  } while (!input);

#ifndef NBTORLOG
  char *a;
  BtorBitVector *ass;
  ass = (BtorBitVector *) btor_get_bv_model (btor, input);
  a   = btor_bv_to_char_bv (btor->mm, ass);
  BTORLOG (1, "");
  BTORLOG (1, "move");
  BTORLOG (1,
           "  input: %s%s",
           BTOR_IS_REGULAR_NODE (input) ? "" : "-",
           node2string (input));
  BTORLOG (1, "  prev. assignment: %s", a);
  btor_freestr (btor->mm, a);
  a = btor_bv_to_char_bv (btor->mm, assignment);
  BTORLOG (1, "  new   assignment: %s", a);
  btor_freestr (btor->mm, a);
#endif

  update_cone (btor, input, assignment);
  BTOR_PROP_SOLVER (btor)->stats.moves += 1;
  btor_free_bv (btor->mm, assignment);

  return 1;
}

/*------------------------------------------------------------------------*/

static void *
clone_prop_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (btor);
  assert (exp_map);

  BtorPropSolver *slv, *res;

  if (!(slv = BTOR_PROP_SOLVER (btor))) return 0;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorPropSolver));

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

  return res;
}

static void
delete_prop_solver (Btor *btor)
{
  assert (btor);

  BtorPropSolver *slv;

  if (!(slv = BTOR_PROP_SOLVER (btor))) return;

  if (slv->score) btor_delete_ptr_hash_table (slv->score);
  if (slv->roots) btor_delete_ptr_hash_table (slv->roots);

  BTOR_DELETE (btor->mm, slv);
}

/* This is an extra function in order to be able to test completeness
 * via test suite. */
#ifdef NDEBUG
static inline int
#else
int
#endif
sat_prop_solver_aux (Btor *btor, int limit0, int limit1)
{
  assert (btor);

  int j, max_steps;
  int sat_result;
  uint32_t nmoves;
  BtorNode *root;
  BtorHashTableIterator it;
  BtorPropSolver *slv;

  (void) limit0;
  (void) limit1;

  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);

  nmoves = 0;

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
      btor_add_ptr_hash_table (slv->roots, root);
  }

  if (!slv->score && btor->options.prop_use_bandit.val)
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
    if (btor->options.prop_use_bandit.val)
      btor_compute_sls_scores (btor, slv->score);

    if (all_constraints_sat (btor)) goto SAT;

    for (j = 0, max_steps = BTOR_PROP_MAXSTEPS (slv->stats.restarts + 1);
         !btor->options.prop_use_restarts.val || j < max_steps;
         j++)
    {
      if (btor_terminate_btor (btor))
      {
        sat_result = BTOR_UNKNOWN;
        goto DONE;
      }

      if (!(move (btor, nmoves))) goto UNSAT;
      nmoves += 1;

      if (all_constraints_sat (btor)) goto SAT;
    }

    /* restart */
    slv->api.generate_model (btor, 0, 1);
    if (btor->options.prop_use_bandit.val)
    {
      btor_delete_ptr_hash_table (slv->score);
      slv->score =
          btor_new_ptr_hash_table (btor->mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);
    }
    slv->stats.restarts += 1;
  }

SAT:
  sat_result = BTOR_SAT;
  goto DONE;

UNSAT:
  sat_result = BTOR_UNSAT;

DONE:
  btor->valid_assignments = 1;
  if (slv->roots)
  {
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

/* Note: failed assumptions -> no handling necessary, prop only works for SAT
 * Note: limits are currently unused */
static int
sat_prop_solver (Btor *btor, int limit0, int limit1)
{
  assert (btor);

  double start;
  int sat_result;

  (void) limit0;
  (void) limit1;

  start = btor_time_stamp ();

  if (btor->inconsistent)
  {
    sat_result = BTOR_UNSAT;
    goto DONE;
  }

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
      "prop engine supports QF_BV only");

  if (btor->inconsistent)
  {
    sat_result = BTOR_UNSAT;
    goto DONE;
  }

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_UNKNOWN;
    goto DONE;
  }

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  BTOR_PROP_SOLVER (btor)->api.generate_model (btor, 0, 1);
  sat_result = sat_prop_solver_aux (btor, limit0, limit1);
DONE:
  BTOR_PROP_SOLVER (btor)->time.sat += btor_time_stamp () - start;
  return sat_result;
}

static void
generate_model_prop_solver (Btor *btor, int model_for_all_nodes, int reset)
{
  assert (btor);

  if (!reset && btor->bv_model) return;
  btor_init_bv_model (btor, &btor->bv_model);
  btor_init_fun_model (btor, &btor->fun_model);
  btor_generate_model (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

static void
print_stats_prop_solver (Btor *btor)
{
  assert (btor);

  BtorPropSolver *slv;

  if (!(slv = BTOR_PROP_SOLVER (btor))) return;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "restarts: %d", slv->stats.restarts);
  BTOR_MSG (btor->msg, 1, "moves: %d", slv->stats.moves);
  BTOR_MSG (btor->msg,
            1,
            "moves per second: %.2f",
            (double) slv->stats.moves / slv->time.sat);
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "propagation move conflicts (recoverable): %d",
            slv->stats.move_prop_rec_conf);
  BTOR_MSG (btor->msg,
            1,
            "propagation move conflicts (non-recoverable): %d",
            slv->stats.move_prop_non_rec_conf);
}

static void
print_time_stats_prop_solver (Btor *btor)
{
  assert (btor);

  BtorPropSolver *slv;

  if (!(slv = BTOR_PROP_SOLVER (btor))) return;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "%.2f seconds for sat call", slv->time.sat);
  BTOR_MSG (btor->msg, 1, "");
}

BtorSolver *
btor_new_prop_solver (Btor *btor)
{
  assert (btor);

  BtorPropSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind = BTOR_PROP_SOLVER_KIND;

  slv->api.clone            = clone_prop_solver;
  slv->api.delet            = delete_prop_solver;
  slv->api.sat              = sat_prop_solver;
  slv->api.generate_model   = generate_model_prop_solver;
  slv->api.print_stats      = print_stats_prop_solver;
  slv->api.print_time_stats = print_time_stats_prop_solver;

  BTOR_MSG (btor->msg, 1, "enabled prop engine");

  return (BtorSolver *) slv;
}

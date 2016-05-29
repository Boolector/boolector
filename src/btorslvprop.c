/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvprop.h"

#include "btorabort.h"
#include "btorbitvec.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorexp.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btoropt.h"
#include "btorslvsls.h"  // currently needed, TODO maybe get rid of in the future

#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

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
  assert (!btor_is_bv_const_node (exp->e[0])
          || (exp->arity > 1 && !btor_is_bv_const_node (exp->e[1])));

  int i, eidx;

  for (i = 0, eidx = -1; i < exp->arity; i++)
    if (btor_is_bv_const_node (exp->e[i]))
    {
      eidx = i ? 0 : 1;
      break;
    }
  assert (exp->arity == 1 || !btor_is_bv_const_node (exp->e[i ? 0 : 1]));
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
    else if (btor_get_opt (btor, BTOR_OPT_PROP_USE_FULL_PATH))
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
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_FULL_PATH))
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
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_FULL_PATH))
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
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_FULL_PATH))
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

  uint32_t ctz_bvmul;
  int eidx, lsbve0, lsbve1;
  bool iszerobve0, iszerobve1;

  eidx = select_path_non_const (mul);

  if (eidx == -1)
  {
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_FULL_PATH))
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
        ctz_bvmul = btor_get_num_trailing_zeros_bv (bvmul);
        if (ctz_bvmul < btor_get_num_trailing_zeros_bv (bve[0])) eidx = 0;
        if (ctz_bvmul < btor_get_num_trailing_zeros_bv (bve[1]))
          eidx = eidx == -1 ? 1 : -1;
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
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_FULL_PATH))
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
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_FULL_PATH))
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
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_FULL_PATH))
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

  assert (!btor_is_bv_const_node (slice->e[0]));

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

#ifdef NDEBUG
static inline BtorBitVector *inv_slice_bv (Btor *,
                                           BtorNode *,
                                           BtorBitVector *,
                                           BtorBitVector *);
#endif

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
  assert (!btor_is_bv_const_node (add->e[eidx]));

  (void) add;
  (void) bve;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_add++;
#endif
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
  assert (!btor_is_bv_const_node (and->e[eidx]));

  uint32_t i;
  BtorBitVector *res;

  (void) and;
  (void) bve;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_and++;
#endif
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
  assert (bveq->width == 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (eq->e[eidx]));

  (void) eq;
  (void) bveq;
  (void) bve;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_eq++;
#endif
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
  assert (bvult->width == 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BtorBitVector *bvmax, *zero, *tmp, *res;

  (void) ult;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_ult++;
#endif
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
  assert (!btor_is_bv_const_node (sll->e[eidx]));

  uint32_t i, s, bw, sbw, ctz_bvsll;
  BtorBitVector *res, *from, *to, *shift;

  (void) sll;
  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_sll++;
#endif
  bw  = bvsll->width;
  sbw = btor_log_2_util (bw);

  ctz_bvsll = btor_get_num_trailing_zeros_bv (bvsll);
  from      = btor_new_bv (btor->mm, sbw);
  to        = btor_uint64_to_bv (
      btor->mm, ctz_bvsll == bw ? ctz_bvsll - 1 : ctz_bvsll, sbw);
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
  assert (!btor_is_bv_const_node (srl->e[eidx]));

  uint32_t i, s, bw, sbw;
  BtorBitVector *res, *from, *to, *shift;

  (void) srl;
  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_srl++;
#endif
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
  assert (!btor_is_bv_const_node (mul->e[eidx]));

  uint32_t r, bw, ctz_res, ctz_bvmul;
  BtorBitVector *res, *tmp;

  (void) mul;
  (void) bve;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_mul++;
#endif
  bw  = bvmul->width;
  res = btor_new_random_bv (btor->mm, &btor->rng, bw);
  if (!btor_is_zero_bv (bvmul))
  {
    if (btor_is_zero_bv (res))
    {
      btor_free_bv (btor->mm, res);
      res = btor_new_random_bv (btor->mm, &btor->rng, bw);
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
      ctz_bvmul = btor_get_num_trailing_zeros_bv (bvmul);
      /* choose res as 2^n with ctz(bvmul) >= ctz(res) with prob 0.1 */
      if (btor_pick_with_prob_rng (&btor->rng, 100))
      {
        btor_free_bv (btor->mm, res);
        res = btor_new_bv (btor->mm, bw);
        btor_set_bit_bv (
            res, btor_pick_rand_rng (&btor->rng, 0, ctz_bvmul - 1), 1);
      }
      /* choose res as bvmul / 2^n with prob 0.1
       * (note: bw not necessarily power of 2 -> do not use srl) */
      else if (btor_pick_with_prob_rng (&btor->rng, 100))
      {
        btor_free_bv (btor->mm, res);
        if ((r = btor_pick_rand_rng (&btor->rng, 0, ctz_bvmul)))
        {
          tmp = btor_slice_bv (btor->mm, bvmul, bw - 1, r);
          res = btor_uext_bv (btor->mm, tmp, r);
          btor_free_bv (btor->mm, tmp);
        }
        else
        {
          res = btor_copy_bv (btor->mm, bvmul);
        }
      }
      /* choose random value with ctz(bvmul) >= ctz(res) with prob 0.8 */
      else
      {
        ctz_res = btor_get_num_trailing_zeros_bv (res);
        if (ctz_res > ctz_bvmul)
          btor_set_bit_bv (
              res, btor_pick_rand_rng (&btor->rng, 0, ctz_bvmul - 1), 1);
      }
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
  assert (!btor_is_bv_const_node (udiv->e[eidx]));

  uint32_t bw;
  BtorBitVector *res, *tmp, *tmpbve, *zero, *one, *bvmax;

  bw    = bvudiv->width;
  zero  = btor_new_bv (btor->mm, bw);
  one   = btor_one_bv (btor->mm, bw);
  bvmax = btor_ones_bv (btor->mm, bw);

  (void) udiv;
  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_udiv++;
#endif
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
  btor_free_bv (btor->mm, zero);
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
  assert (!btor_is_bv_const_node (urem->e[eidx]));

  uint32_t bw;
  BtorBitVector *res, *bvmax, *tmp;

  (void) urem;
  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_urem++;
#endif
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
  assert (concat);
  assert (BTOR_IS_REGULAR_NODE (concat));
  assert (bvconcat);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (concat->e[eidx]));

  (void) concat;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_concat++;
#endif
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
#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_slice++;
#endif
  return inv_slice_bv (btor, slice, bvslice, bve);
}

/*------------------------------------------------------------------------*/

#define BTOR_INC_REC_CONF_STATS(btor, inc)                              \
  do                                                                    \
  {                                                                     \
    if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)       \
      BTOR_PROP_SOLVER (btor)->stats.move_prop_rec_conf += inc;         \
    else                                                                \
    {                                                                   \
      assert (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS); \
      BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += inc;          \
    }                                                                   \
  } while (0)

#define BTOR_INC_NON_REC_CONF_STATS(btor, inc)                          \
  do                                                                    \
  {                                                                     \
    if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)       \
      BTOR_PROP_SOLVER (btor)->stats.move_prop_non_rec_conf += inc;     \
    else                                                                \
    {                                                                   \
      assert (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS); \
      BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += inc;      \
    }                                                                   \
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
  BTOR_INC_NON_REC_CONF_STATS (btor, 1);
  return 0;
}

#ifndef NDEBUG
static inline void
check_result_binary_dbg (Btor *btor,
                         BtorBitVector *(*fun) (BtorMemMgr *,
                                                const BtorBitVector *,
                                                const BtorBitVector *),
                         BtorNode *exp,
                         BtorBitVector *bve,
                         BtorBitVector *bvexp,
                         BtorBitVector *res,
                         int eidx,
                         char *op)
{
  assert (btor);
  assert (fun);
  assert (exp);
  assert (bve);
  assert (bvexp);
  assert (res);
  assert (op);

  (void) exp;
  (void) op;

  BtorBitVector *tmp;
  char *sbve, *sbvexp, *sres;

  tmp = eidx ? fun (btor->mm, bve, res) : fun (btor->mm, res, bve);
  assert (!btor_compare_bv (tmp, bvexp));
  sbvexp = btor_bv_to_char_bv (btor->mm, bvexp);
  sbve   = btor_bv_to_char_bv (btor->mm, bve);
  sres   = btor_bv_to_char_bv (btor->mm, res);
  BTORLOG (3,
           "prop (e[%d]): %s: %s := %s %s %s",
           eidx,
           node2string (exp),
           sbvexp,
           eidx ? sbve : sres,
           op,
           eidx ? sres : sbve);
  btor_free_bv (btor->mm, tmp);
  btor_freestr (btor->mm, sbvexp);
  btor_freestr (btor->mm, sbve);
  btor_freestr (btor->mm, sres);
}
#endif

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
  assert (add);
  assert (BTOR_IS_REGULAR_NODE (add));
  assert (bvadd);
  assert (bve);
  assert (bve->width == bvadd->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (add->e[eidx]));

  BtorBitVector *res;
  BtorMemMgr *mm;

  (void) add;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_add++;
#endif

  mm = btor->mm;
  /* res + bve = bve + res = bvadd -> res = bvadd - bve */
  res = btor_sub_bv (mm, bvadd, bve);
#ifndef NDEBUG
  check_result_binary_dbg (btor, btor_add_bv, add, bve, bvadd, res, eidx, "+");
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
  assert (and);
  assert (BTOR_IS_REGULAR_NODE (and));
  assert (bvand);
  assert (bve);
  assert (bve->width == bvand->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (and->e[eidx]));

  uint32_t i;
  int bitand, bite;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int iscon = 0;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_and++;
#endif
  mm = btor->mm;
  e  = and->e[eidx ? 0 : 1];
  assert (e);

  res = btor_new_bv (mm, bvand->width);

  for (i = 0; i < bvand->width; i++)
  {
    bitand = btor_get_bit_bv (bvand, i);
    bite   = btor_get_bit_bv (bve, i);

    /* CONFLICT: all bits set in bvand, must be set in bve -------------- */
    if (bitand&&!bite)
    {
      btor_free_bv (btor->mm, res);
      /* check for non-recoverable conflict */
      if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
          && btor_is_bv_const_node (e))
      {
        res = non_rec_conf (btor, bve, bvand, eidx, "AND");
      }
      else
      {
        res = cons_and_bv (btor, and, bvand, bve, eidx);
        BTOR_INC_REC_CONF_STATS (btor, 1);
      }
#ifndef NDEBUG
      iscon = 1;
#endif
      break;
    }
    /* ^^--------------------------------------------------------------^^ */

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

#ifndef NDEBUG
  if (!iscon)
    check_result_binary_dbg (
        btor, btor_and_bv, and, bve, bvand, res, eidx, "AND");
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
  assert (eq);
  assert (BTOR_IS_REGULAR_NODE (eq));
  assert (bveq);
  assert (bveq->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (eq->e[eidx]));

  BtorBitVector *res;
  BtorMemMgr *mm;

  (void) eq;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_eq++;
#endif
  mm = btor->mm;

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
  check_result_binary_dbg (btor, btor_eq_bv, eq, bve, bveq, res, eidx, "=");
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
  assert (ult);
  assert (BTOR_IS_REGULAR_NODE (ult));
  assert (bvult);
  assert (bvult->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BtorNode *e;
  BtorBitVector *res, *zero, *one, *bvmax, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int iscon = 0;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_ult++;
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
    /* CONFLICT: 1...1 < e[1] ------------------------------------------- */
    if (!btor_compare_bv (bve, bvmax) && isult)
    {
    BVULT_CONF:
      /* check for non-recoverable conflict */
      if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
          && btor_is_bv_const_node (e))
      {
        res = non_rec_conf (btor, bve, bvult, eidx, "<");
      }
      else
      {
        res = cons_ult_bv (btor, ult, bvult, bve, eidx);
        BTOR_INC_REC_CONF_STATS (btor, 1);
      }
#ifndef NDEBUG
      iscon = 1;
#endif
    }
    /* ^^---------------------------------------------------------------^^ */
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
    /* CONFLICT: e[0] < 0 ----------------------------------------------- */
    if (btor_is_zero_bv (bve) && isult)
    {
      goto BVULT_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
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
    check_result_binary_dbg (
        btor, btor_ult_bv, ult, bve, bvult, res, eidx, "<");
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
  assert (sll);
  assert (BTOR_IS_REGULAR_NODE (sll));
  assert (bvsll);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsll->width);
  assert (eidx || btor_log_2_util (bvsll->width) == bve->width);
  assert (!btor_is_bv_const_node (sll->e[eidx]));

  uint32_t i, j, ctz_bve, ctz_bvsll, shift, sbw;
  BtorNode *e;
  BtorBitVector *res, *tmp, *bvmax;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int iscon = 0;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_sll++;
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

        /* CONFLICT: do not allow shift by bw ----------------------- */
        if (shift > bvsll->width - 1)
        {
          assert (btor_is_zero_bv (bvsll));
        BVSLL_CONF:
          /* check for non-recoverable conflict */
          if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
              && btor_is_bv_const_node (e))
          {
            res = non_rec_conf (btor, bve, bvsll, eidx, "<<");
          }
          else
          {
            res = cons_sll_bv (btor, sll, bvsll, bve, eidx);
            BTOR_INC_REC_CONF_STATS (btor, 1);
          }
#ifndef NDEBUG
          iscon = 1;
#endif
        }
        /* ^^------------------------------------------------------^^ */
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
          /* CONFLICT: shifted bits must match -------------------- */
          for (i = 0, j = shift, res = 0; i < bve->width - j; i++)
          {
            if (btor_get_bit_bv (bve, i) != btor_get_bit_bv (bvsll, j + i))
              goto BVSLL_CONF;
          }
          /* ^^--------------------------------------------------^^ */

          res = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
        }
      }
      else
      {
        goto BVSLL_CONF;
      }
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

    /* CONFLICT: the LSBs shifted must be zero -------------------------- */
    if (btor_get_num_trailing_zeros_bv (bvsll) < shift) goto BVSLL_CONF;
    /* ^^--------------------------------------------------------------^^ */

    res = btor_srl_bv (mm, bvsll, bve);
    for (i = 0; i < shift; i++)
      btor_set_bit_bv (
          res, res->width - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }
#ifndef NDEBUG
  if (!iscon)
    check_result_binary_dbg (
        btor, btor_sll_bv, sll, bve, bvsll, res, eidx, "<<");
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
  assert (srl);
  assert (BTOR_IS_REGULAR_NODE (srl));
  assert (bvsrl);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsrl->width);
  assert (eidx || btor_log_2_util (bvsrl->width) == bve->width);
  assert (!btor_is_bv_const_node (srl->e[eidx]));

  uint32_t i, j, clz_bve, clz_bvsrl, shift, sbw;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int iscon = 0;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_srl++;
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

        /* CONFLICT: do not allow shift by bw ----------------------- */
        if (shift > bvsrl->width - 1)
        {
          assert (btor_is_zero_bv (bvsrl));
        BVSRL_CONF:
          /* check for non-recoverable conflict */
          if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
              && btor_is_bv_const_node (e))
          {
            res = non_rec_conf (btor, bve, bvsrl, eidx, ">>");
          }
          else
          {
            res = cons_srl_bv (btor, srl, bvsrl, bve, eidx);
            BTOR_INC_REC_CONF_STATS (btor, 1);
          }
#ifndef NDEBUG
          iscon = 1;
#endif
        }
        /* ^^------------------------------------------------------^^ */
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
          /* CONFLICT: shifted bits must match -------------------- */
          for (i = 0, j = shift, res = 0; i < bve->width - j; i++)
          {
            if (btor_get_bit_bv (bve, bve->width - 1 - i)
                != btor_get_bit_bv (bvsrl, bvsrl->width - 1 - (j + i)))
              goto BVSRL_CONF;
          }
          /* ^^--------------------------------------------------^^ */

          res = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
        }
      }
      else
      {
        goto BVSRL_CONF;
      }
    }
  }
  /* e[0] >> bve = bvsll
   * -> e[0] = bvsll << bve
   *    set irrelevant LSBs (the ones that get shifted out) randomly */
  else
  {
    /* cast is no problem (max bit width handled by Boolector is INT_MAX) */
    shift = (int) btor_bv_to_uint64_bv (bve);

    /* CONFLICT: the MSBs shifted must be zero -------------------------- */
    if (btor_get_num_leading_zeros_bv (bvsrl) < shift) goto BVSRL_CONF;
    /* ^^--------------------------------------------------------------^^ */

    res = btor_sll_bv (mm, bvsrl, bve);
    for (i = 0; i < shift; i++)
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }

#ifndef NDEBUG
  if (!iscon)
    check_result_binary_dbg (
        btor, btor_srl_bv, srl, bve, bvsrl, res, eidx, ">>");
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
  assert (mul);
  assert (BTOR_IS_REGULAR_NODE (mul));
  assert (bvmul);
  assert (bve);
  assert (bve->width == bvmul->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (mul->e[eidx]));

  int lsbve, lsbvmul, ispow2_bve;
  uint32_t i, j, bw;
  BtorBitVector *res, *inv, *tmp, *tmp2;
  BtorMemMgr *mm;
  BtorNode *e;
#ifndef NDEBUG
  int iscon = 0;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_mul++;
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
    /* CONFLICT: bve = 0 but bvmul != 0 -------------------------------- */
    else
    {
    BVMUL_CONF:
      /* check for non-recoverable conflict */
      if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
          && btor_is_bv_const_node (e))
      {
        res = non_rec_conf (btor, bve, bvmul, eidx, "*");
      }
      else
      {
        res = cons_mul_bv (btor, mul, bvmul, bve, eidx);
        BTOR_INC_REC_CONF_STATS (btor, 1);
      }
#ifndef NDEBUG
      iscon = 1;
#endif
    }
    /* ^^-------------------------------------------------------------^^ */
  }
  /* CONFLICT: bvmul odd and bve ----------------------------------------- */
  else if (lsbvmul && !lsbve)
  {
    goto BVMUL_CONF;
  }
  /* ^^-----------------------------------------------------------------^^ */
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
      if ((ispow2_bve = btor_power_of_two_bv (bve)) >= 0)
      {
        for (i = 0; i < bw; i++)
          if (btor_get_bit_bv (bvmul, i)) break;
        /* CONFLICT: number of 0-LSBs in bvmul < n (for bve = 2^n) -- */
        if (i < (uint32_t) ispow2_bve)
        {
          goto BVMUL_CONF;
        }
        /* ^^------------------------------------------------------^^ */
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
        /* CONFLICT: number of 0-LSB in bvmul < number of 0-LSB in bve */
        if (i < j)
        {
          goto BVMUL_CONF;
        }
        /* ^^-------------------------------------------------------^^ */
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
    check_result_binary_dbg (
        btor, btor_mul_bv, mul, bve, bvmul, res, eidx, "*");
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
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);
  assert (bve->width == bvudiv->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (udiv->e[eidx]));

  uint32_t bw;
  BtorNode *e;
  BtorBitVector *res, *lo, *up, *one, *bvmax, *tmp;
  BtorMemMgr *mm;
  BtorRNG *rng;
#ifndef NDEBUG
  int iscon = 0;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_udiv++;
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
          && btor_pick_with_prob_rng (&btor->rng, 500))
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
      /* CONFLICT ----------------------------------------------------- */
      else
      {
      BVUDIV_CONF:
        /* check for non-recoverable conflict */
        if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
            && btor_is_bv_const_node (e))
        {
          res = non_rec_conf (btor, bve, bvudiv, eidx, "/");
        }
        else
        {
          res = cons_udiv_bv (btor, udiv, bvudiv, bve, eidx);
          BTOR_INC_REC_CONF_STATS (btor, 1);
        }
#ifndef NDEBUG
        iscon = 1;
#endif
      }
      /* ^^----------------------------------------------------------^^ */
    }
    /* CONFLICT: bve < bvudiv ------------------------------------------- */
    else if (btor_compare_bv (bve, bvudiv) < 0)
    {
      goto BVUDIV_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
    else
    {
      /* if bvudiv is a divisor of bve, choose e[1] = bve / bvudiv
       * with prob = 0.5 and a bve s.t. bve / e[1] = bvudiv otherwise */
      tmp = btor_urem_bv (mm, bve, bvudiv);
      if (btor_is_zero_bv (tmp) && btor_pick_with_prob_rng (rng, 500))
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

        /* CONFLICT: lo > up ---------------------------------------- */
        if (btor_compare_bv (lo, up) > 0)
        {
          btor_free_bv (mm, lo);
          btor_free_bv (mm, up);
          goto BVUDIV_CONF;
        }
        /* ^^------------------------------------------------------^^ */
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
      /* CONFLICT ---------------------------------------------------- */
      else
      {
        goto BVUDIV_CONF;
      }
      /* ^^---------------------------------------------------------^^ */
    }
    /* CONFLICT: bve = 0 and bvudiv < 2^bw - 1 ------------------------- */
    else if (btor_is_zero_bv (bve))
    {
      goto BVUDIV_CONF;
    }
    /* ^^-------------------------------------------------------------^^ */
    else
    {
      /* if bve * bvudiv does not overflow, choose e[0] = bve * bvudiv
       * with prob = 0.5 and a bve s.t. e[0] / bve = bvudiv otherwise */

      /* CONFLICT: overflow: bve * bvudiv ----------------------------- */
      if (btor_is_umulo_bv (mm, bve, bvudiv)) goto BVUDIV_CONF;
      /* ^^----------------------------------------------------------^^ */
      else
      {
        if (btor_pick_with_prob_rng (rng, 500))
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
    check_result_binary_dbg (
        btor, btor_udiv_bv, udiv, bve, bvudiv, res, eidx, "/");
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
  assert (urem);
  assert (BTOR_IS_REGULAR_NODE (urem));
  assert (bvurem);
  assert (bve);
  assert (bve->width == bvurem->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (urem->e[eidx]));

  uint32_t bw, cnt;
  int cmp;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp, *tmp2, *one, *n, *mul, *up, *sub;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int iscon = 0;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_urem++;
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
      /* CONFLICT: bvurem = 1...1 but bve != 1...1 -------------------- */
      if (btor_compare_bv (bve, bvmax))
      {
      BVUREM_CONF:
        /* check for non-recoverable conflict */
        if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
            && btor_is_bv_const_node (e))
        {
          res = non_rec_conf (btor, bve, bvurem, eidx, "%");
        }
        else
        {
          res = cons_urem_bv (btor, urem, bvurem, bve, eidx);
          BTOR_INC_REC_CONF_STATS (btor, 1);
        }
#ifndef NDEBUG
        iscon = 1;
#endif
      }
      /* ^^----------------------------------------------------------^^ */
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
        /* choose e[1] = 0 with prob = 0.25*/
        if (btor_pick_with_prob_rng (&btor->rng, 250))
          res = btor_new_bv (mm, bw);
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
          /* CONFLICT: -------------------------------------------- */
          /* bvurem = bve - 1 -> bve % e[1] = bve - 1
           * -> not possible if bvurem > 0  */
          if (!btor_compare_bv (bvurem, tmp))
          {
            btor_free_bv (mm, tmp);
            goto BVUREM_CONF;
          }
          /* ^^--------------------------------------------------^^ */
          btor_free_bv (mm, tmp);
        }

        sub = btor_sub_bv (mm, bve, bvurem);

        /* CONFLICT: bve - bvurem <= bvurem ------------------------- */
        if (btor_compare_bv (sub, bvurem) <= 0)
        {
          btor_free_bv (mm, sub);
          goto BVUREM_CONF;
        }
        /* ^^------------------------------------------------------^^ */
        /* choose either n = 1 or 1 <= n < (bve - bvurem) / bvurem
         * with prob = 0.5 */
        else
        {
          if (btor_pick_with_prob_rng (&btor->rng, 500))
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
      /* CONFLICT: bve < bvurem --------------------------------------- */
      else
      {
        goto BVUREM_CONF;
      }
      /* ^^----------------------------------------------------------^^ */
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
    /* CONFLICT: bvurem > 0 and bve = 1 --------------------------------- */
    else if (!btor_is_zero_bv (bvurem) && btor_is_one_bv (bve))
    {
      goto BVUREM_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
    /* bvurem = 1...1 -> bve = 0, e[0] = 1...1 */
    else if (!btor_compare_bv (bvurem, bvmax))
    {
      /* CONFLICT: bve != 0 ------------------------------------------- */
      if (!btor_is_zero_bv (bve))
      {
        goto BVUREM_CONF;
      }
      /* ^^----------------------------------------------------------^^ */
      else
      {
        goto BVUREM_ZERO_0;
      }
    }
    else if (btor_compare_bv (bve, bvurem) > 0)
    {
      /* choose simplest solution (0 <= res < bve -> res = bvurem)
       * with prob 0.5 */
      if (btor_pick_with_prob_rng (&btor->rng, 500))
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
    /* CONFLICT: bve <= bvurem ------------------------------------------ */
    else
    {
      goto BVUREM_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
  }

  btor_free_bv (mm, one);
  btor_free_bv (mm, bvmax);

#ifndef NDEBUG
  if (!iscon)
    check_result_binary_dbg (
        btor, btor_urem_bv, urem, bve, bvurem, res, eidx, "%");
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
  assert (concat);
  assert (BTOR_IS_REGULAR_NODE (concat));
  assert (bvconcat);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (concat->e[eidx]));

  BtorNode *e;
  BtorBitVector *res, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int iscon = 0;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_concat++;
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
    /* CONFLICT: bve bits do not match bvconcat ------------------------- */
    if (btor_compare_bv (tmp, bve))
    {
    BVCONCAT_CONF:
      /* check for non-recoverable conflict */
      if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
          && btor_is_bv_const_node (e))
      {
        res = non_rec_conf (btor, bve, bvconcat, eidx, "o");
      }
      else
      {
        res = cons_concat_bv (btor, concat, bvconcat, bve, eidx);
        BTOR_INC_REC_CONF_STATS (btor, 1);
      }
#ifndef NDEBUG
      iscon = 1;
#endif
    }
    /* ^^--------------------------------------------------------------^^ */
    else
    {
      res = btor_slice_bv (mm, bvconcat, bvconcat->width - bve->width - 1, 0);
    }
  }
  /* e[0] o bve = bvconcat, slice e[0] out of the upper bits of bvconcat */
  else
  {
    tmp = btor_slice_bv (mm, bvconcat, bve->width - 1, 0);
    /* CONFLICT: bve bits do not match bvconcat ------------------------- */
    if (btor_compare_bv (tmp, bve))
    {
      goto BVCONCAT_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
    else
    {
      res = btor_slice_bv (mm, bvconcat, bvconcat->width - 1, bve->width);
    }
  }
  btor_free_bv (mm, tmp);
#ifndef NDEBUG
  if (!iscon)
    check_result_binary_dbg (
        btor, btor_concat_bv, concat, bve, bvconcat, res, eidx, "o");
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
  assert (slice);
  assert (BTOR_IS_REGULAR_NODE (slice));
  assert (bvslice);
  assert (!btor_is_bv_const_node (slice->e[0]));

  uint32_t i, upper, lower;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
  bool b;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_slice++;
#endif
  mm = btor->mm;
  e  = slice->e[0];
  assert (e);

  b = btor_pick_with_prob_rng (&btor->rng, 500);

  upper = btor_slice_get_upper (slice);
  lower = btor_slice_get_lower (slice);

  res = btor_new_bv (mm, btor_get_exp_width (btor, e));
  /* keep previous value for don't care bits or set randomly with prob = 0.5 */
  for (i = 0; i < lower; i++)
    btor_set_bit_bv (res,
                     i,
                     b ? btor_get_bit_bv (bve, i)
                       : (int) btor_pick_rand_rng (&btor->rng, 0, 1));
  /* set sliced bits to propagated value */
  for (i = lower; i <= upper; i++)
    btor_set_bit_bv (res, i, btor_get_bit_bv (bvslice, i - lower));
  /* keep previous value for don't care bits or set randomly with prob = 0.5 */
  for (i = upper + 1; i < res->width; i++)
    btor_set_bit_bv (res,
                     i,
                     b ? btor_get_bit_bv (bve, i)
                       : (int) btor_pick_rand_rng (&btor->rng, 0, 1));

#ifndef NDEBUG
  BtorBitVector *tmpdbg = btor_slice_bv (mm, res, upper, lower);
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

uint64_t
btor_select_move_prop (Btor *btor,
                       BtorNode *root,
                       BtorNode **input,
                       BtorBitVector **assignment)
{
  assert (btor);
  assert (root);
  assert (
      btor_bv_to_uint64_bv ((BtorBitVector *) btor_get_bv_model (btor, root))
      == 0);

  bool b;
  int i, nconst, eidx, idx;
  uint64_t props;
  BtorNode *cur, *real_cur;
  BtorBitVector *bve[3], *bvcur, *bvenew, *tmp;

  *input      = 0;
  *assignment = 0;
  props       = 0;

  cur   = root;
  bvcur = btor_one_bv (btor->mm, 1);

  if (btor_is_bv_var_node (cur))
  {
    *input      = BTOR_REAL_ADDR_NODE (cur);
    *assignment = BTOR_IS_INVERTED_NODE (cur) ? btor_not_bv (btor->mm, bvcur)
                                              : btor_copy_bv (btor->mm, bvcur);
  }
  else
  {
    for (;;)
    {
      props += 1;
      real_cur = BTOR_REAL_ADDR_NODE (cur);
      assert (!btor_is_bv_cond_node (real_cur));
      assert (!btor_is_bv_const_node (real_cur));
      assert (!btor_is_bv_var_node (real_cur));
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
        if (btor_is_bv_const_node (real_cur->e[i])) nconst += 1;
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
       * -> if b then inverse else consistent */
      b = btor_pick_with_prob_rng (
          &btor->rng, btor_get_opt (btor, BTOR_OPT_PROP_USE_INV_VALUE_PROB));

      /* select path and determine path assignment */
      switch (real_cur->kind)
      {
        case BTOR_ADD_NODE:
          eidx = select_path_add (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_add_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_add_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_AND_NODE:
          eidx = select_path_and (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_and_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_and_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_BV_EQ_NODE:
          eidx = select_path_eq (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_eq_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_eq_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_ULT_NODE:
          eidx = select_path_ult (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_ult_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_ult_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_SLL_NODE:
          eidx = select_path_sll (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_sll_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_sll_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_SRL_NODE:
          eidx = select_path_srl (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_srl_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_srl_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_MUL_NODE:
          eidx = select_path_mul (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_mul_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_mul_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_UDIV_NODE:
          eidx = select_path_udiv (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_udiv_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_udiv_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_UREM_NODE:
          eidx = select_path_urem (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_urem_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_urem_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_CONCAT_NODE:
          eidx = select_path_concat (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_concat_bv (btor, real_cur, bvcur, bve[idx], eidx)
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
      if (btor_is_bv_var_node (real_cur->e[eidx]))
      {
      FOUND_RESULT:
        *input      = BTOR_REAL_ADDR_NODE (cur);
        *assignment = BTOR_IS_INVERTED_NODE (cur)
                          ? btor_not_bv (btor->mm, bvenew)
                          : btor_copy_bv (btor->mm, bvenew);
        btor_free_bv (btor->mm, bvenew);
        break;
      }
      else if (btor_is_bv_cond_node (real_cur->e[eidx]))
      {
        real_cur = BTOR_REAL_ADDR_NODE (cur);
        do
        {
          /* either assume that cond is fixed and propagate bvenew
           * to enabled path, or flip condition */

          tmp = (BtorBitVector *) btor_get_bv_model (btor, real_cur->e[0]);

          if (btor_pick_with_prob_rng (
                  &btor->rng,
                  btor_get_opt (btor, BTOR_OPT_PROP_FLIP_COND_PROB)))
          {
            /* flip condition */
            btor_free_bv (btor->mm, bvenew);
            bvenew = btor_not_bv (btor->mm, tmp);
            cur    = real_cur->e[0];
          }
          else
          {
            /* assume cond to be fixed */
            cur = btor_is_zero_bv (tmp) ? real_cur->e[2] : real_cur->e[1];
          }

          real_cur = BTOR_REAL_ADDR_NODE (cur);
        } while (btor_is_bv_cond_node (real_cur));

        if (btor_is_bv_var_node (cur))
        {
          goto FOUND_RESULT;
        }
        else if (btor_is_bv_const_node (cur))
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
  return props;
}

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

static void
update_cone (Btor *btor, BtorNode *exp, BtorBitVector *assignment)
{
  assert (btor);
  assert (BTOR_PROP_SOLVER (btor));
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_bv_var_node (exp));
  assert (assignment);

  double start, delta;
  uint32_t i, j;
  BtorNode *cur;
  BtorNodeIterator nit;
  BtorPtrHashTable *bv_model, *score;
  BtorPtrHashBucket *b;
  BtorNodePtrStack stack, cone;
  BtorIntHashTable *cache;
  BtorPropSolver *slv;
  BtorBitVector *bv, *e[3];
  BtorMemMgr *mm;

  start = delta = btor_time_stamp ();

  mm       = btor->mm;
  bv_model = btor->bv_model;
  assert (bv_model);
  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  score = slv->score;
  assert (!btor_get_opt (btor, BTOR_OPT_PROP_USE_BANDIT) || score);

#ifndef NDEBUG
  BtorHashTableIterator it;
  BtorNode *root;
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    if (btor_is_false_bv (btor_get_bv_model (btor, root)))
      assert (btor_contains_int_hash_map (slv->roots, BTOR_GET_ID_NODE (root)));
    else
      assert (
          !btor_contains_int_hash_map (slv->roots, BTOR_GET_ID_NODE (root)));
  }
#endif

  /* reset cone */
  BTOR_INIT_STACK (cone);
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, exp);
  cache = btor_new_int_hash_table (mm);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (btor_contains_int_hash_table (cache, cur->id)) continue;
    btor_add_int_hash_table (cache, cur->id);
    if (cur != exp) BTOR_PUSH_STACK (mm, cone, cur);
    slv->stats.updates += 1;

    // FIXME update score similarly to assignments
    // (individually, do not remove from hash table)
    //
    /* reset previous score */
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_BANDIT))
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

  BTOR_PROP_SOLVER (btor)->time.update_cone_reset += btor_time_stamp () - delta;
  delta = btor_time_stamp ();

  /* update assignment of exp */
  b = btor_get_ptr_hash_table (bv_model, exp);
  assert (b);
  if ((exp->constraint || btor_get_ptr_hash_table (btor->assumptions, exp)
       || btor_get_ptr_hash_table (btor->assumptions, BTOR_INVERT_NODE (exp)))
      && btor_compare_bv (b->data.as_ptr, assignment))
  {
    /* old assignment != new assignment */
    update_roots (btor, slv->roots, exp, assignment);
  }
  btor_free_bv (mm, b->data.as_ptr);
  b->data.as_ptr = btor_copy_bv (mm, assignment);
  if ((b = btor_get_ptr_hash_table (bv_model, BTOR_INVERT_NODE (exp))))
  {
    btor_free_bv (mm, b->data.as_ptr);
    b->data.as_ptr = btor_not_bv (mm, assignment);
  }

  /* update cone */
  qsort (cone.start,
         BTOR_COUNT_STACK (cone),
         sizeof (BtorNode *),
         btor_cmp_exp_by_id_qsort_asc);
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
        update_roots (btor, slv->roots, cur, bv);
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
  BTOR_RELEASE_STACK (btor->mm, cone);
  BTOR_PROP_SOLVER (btor)->time.update_cone_model_gen +=
      btor_time_stamp () - delta;

  if (btor_get_opt (btor, BTOR_OPT_PROP_USE_BANDIT))
  {
    delta = btor_time_stamp ();
    btor_compute_sls_scores (btor, BTOR_PROP_SOLVER (btor)->score);
    BTOR_PROP_SOLVER (btor)->time.update_cone_compute_score +=
        btor_time_stamp () - delta;
  }

#ifndef NDEBUG
  printf ("---\n");
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    printf ("adfasdf %s\n", node2string (root));
    if (btor_is_false_bv (btor_get_bv_model (btor, root)))
      assert (btor_contains_int_hash_map (slv->roots, BTOR_GET_ID_NODE (root)));
    else
      assert (
          !btor_contains_int_hash_map (slv->roots, BTOR_GET_ID_NODE (root)));
  }
#endif
  BTOR_PROP_SOLVER (btor)->time.update_cone += btor_time_stamp () - start;
}

static BtorNode *
select_constraint (Btor *btor, uint32_t nmoves)
{
  assert (btor);

  BtorNode *res, *cur;
  BtorPropSolver *slv;

  size_t i;
  int32_t id;
  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  assert (slv->roots);
  assert (slv->roots->count);

#ifndef NDEBUG
  BtorHashTableIterator it;
  BtorNode *root;
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    printf ("select adsf %s\n", node2string (root));
    if (btor_is_false_bv (btor_get_bv_model (btor, root)))
      assert (btor_contains_int_hash_map (slv->roots, BTOR_GET_ID_NODE (root)));
    else
      assert (
          !btor_contains_int_hash_map (slv->roots, BTOR_GET_ID_NODE (root)));
  }
#endif

  res = 0;

  if (btor_get_opt (btor, BTOR_OPT_PROP_USE_BANDIT))
  {
    assert (slv->score);

    int *selected;
    double value, max_value, score;
    BtorPtrHashBucket *b;
    max_value = 0.0;
    for (i = 0; i < slv->roots->size; i++)
    {
      if (!(id = slv->roots->keys[i])) continue;

      cur      = btor_get_node_by_id (btor, id);
      selected = &slv->roots->data[i].as_int;

      b = btor_get_ptr_hash_table (slv->score, cur);
      assert (b);
      score = b->data.as_dbl;
      assert (score < 1.0);

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
    size_t j, r;

    r = btor_pick_rand_rng (&btor->rng, 0, slv->roots->count - 1);
    for (i = 0, j = 0; j <= r; i++)
    {
      assert (i < slv->roots->size);
      if (!slv->roots->keys[i]) continue;
      res = btor_get_node_by_id (btor, slv->roots->keys[i]);
      j++;
    }
    assert (!btor_is_bv_const_node (res));
  }

  assert (res);
  assert (btor_is_zero_bv (btor_get_bv_model (btor, res)));

  BTORLOG (1, "");
  BTORLOG (1, "select constraint: %s", node2string (res));

  return res;
}

static int
move (Btor *btor, uint32_t nmoves)
{
  assert (btor);

  BTORLOG (1, "");
  BTORLOG (1, "*** move");

  BtorNode *root, *input;
  BtorBitVector *assignment;

  /* roots contain false constraint -> unsat */
  if (!(root = select_constraint (btor, nmoves))) return 0;

  do
  {
    BTOR_PROP_SOLVER (btor)->stats.props +=
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

static BtorPropSolver *
clone_prop_solver (Btor *clone, BtorPropSolver *slv, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (exp_map);

  BtorPropSolver *res;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorPropSolver));

  res->btor  = clone;
  res->roots = btor_clone_int_hash_map (clone->mm, slv->roots, 0, 0);
  res->score = btor_clone_ptr_hash_table (clone->mm,
                                          slv->score,
                                          btor_clone_key_as_node,
                                          btor_clone_data_as_dbl,
                                          exp_map,
                                          0);

  return res;
}

static void
delete_prop_solver (BtorPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  if (slv->score) btor_delete_ptr_hash_table (slv->score);
  if (slv->roots) btor_delete_int_hash_map (slv->roots);

  BTOR_DELETE (slv->btor->mm, slv);
}

/* This is an extra function in order to be able to test completeness
 * via test suite. */
#ifdef NDEBUG
static inline int
#else
int
#endif
sat_prop_solver_aux (Btor *btor)
{
  assert (btor);

  int j, max_steps;
  int sat_result;
  uint32_t nmoves, nprops;
  BtorNode *root;
  BtorHashTableIterator it;
  BtorPropSolver *slv;

  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  nprops = btor_get_opt (btor, BTOR_OPT_PROP_NPROPS);

  nmoves = 0;

  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    if (btor_get_ptr_hash_table (btor->unsynthesized_constraints,
                                 BTOR_INVERT_NODE (root)))
      goto UNSAT;
    if (btor_get_ptr_hash_table (btor->assumptions, BTOR_INVERT_NODE (root)))
      goto UNSAT;
  }

  for (;;)
  {
    /* collect unsatisfied roots */
    assert (!slv->roots);
    slv->roots = btor_new_int_hash_map (btor->mm);
    assert (btor->synthesized_constraints->count == 0);
    btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
    btor_queue_node_hash_table_iterator (&it, btor->assumptions);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      root = btor_next_node_hash_table_iterator (&it);
      if (!btor_contains_int_hash_map (slv->roots, BTOR_GET_ID_NODE (root))
          && btor_is_zero_bv (btor_get_bv_model (btor, root)))
      {
        if (btor_is_bv_const_node (root))
          goto UNSAT; /* contains false constraint -> unsat */
        btor_add_int_hash_map (slv->roots, BTOR_GET_ID_NODE (root));
      }
    }

    if (!slv->score && btor_get_opt (btor, BTOR_OPT_PROP_USE_BANDIT))
      slv->score =
          btor_new_ptr_hash_table (btor->mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);

    if (btor_terminate_btor (btor))
    {
      sat_result = BTOR_RESULT_UNKNOWN;
      goto DONE;
    }

    /* all constraints sat? */
    if (!slv->roots->count) goto SAT;

    /* compute initial sls score */
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_BANDIT))
      btor_compute_sls_scores (btor, slv->score);

    /* move */
    for (j = 0, max_steps = BTOR_PROP_MAXSTEPS (slv->stats.restarts + 1);
         !btor_get_opt (btor, BTOR_OPT_PROP_USE_RESTARTS) || j < max_steps;
         j++)
    {
      if (btor_terminate_btor (btor) || (nprops && slv->stats.props >= nprops))
      {
        sat_result = BTOR_RESULT_UNKNOWN;
        goto DONE;
      }

      if (!(move (btor, nmoves))) goto UNSAT;
      nmoves += 1;

      /* all constraints sat? */
      if (!slv->roots->count) goto SAT;
    }

    /* restart */
    slv->api.generate_model ((BtorSolver *) slv, false, true);
    btor_delete_int_hash_map (slv->roots);
    slv->roots = 0;
    if (btor_get_opt (btor, BTOR_OPT_PROP_USE_BANDIT))
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
  sat_result = BTOR_RESULT_SAT;
  goto DONE;

UNSAT:
  sat_result = BTOR_RESULT_UNSAT;

DONE:
  btor->valid_assignments = 1;
  if (slv->roots)
  {
    btor_delete_int_hash_map (slv->roots);
    slv->roots = 0;
  }
  if (slv->score)
  {
    btor_delete_ptr_hash_table (slv->score);
    slv->score = 0;
  }
  return sat_result;
}

/* Note: failed assumptions -> no handling necessary, prop only works for SAT
 * Note: limits are currently unused */
static int
sat_prop_solver (BtorPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  double start, delta = 0;
  int sat_result;
  Btor *btor;

  start = btor_time_stamp ();

  btor = slv->btor;

  if (btor->inconsistent)
  {
    sat_result = BTOR_RESULT_UNSAT;
    goto DONE;
  }

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
              "prop engine supports QF_BV only");

  if (btor->inconsistent)
  {
    sat_result = BTOR_RESULT_UNSAT;
    goto DONE;
  }

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  delta = btor_time_stamp ();

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  slv->api.generate_model ((BtorSolver *) slv, false, true);
  sat_result = sat_prop_solver_aux (btor);
  BTOR_PROP_SOLVER (btor)->time.sat += btor_time_stamp () - delta;
DONE:
  BTOR_PROP_SOLVER (btor)->time.sat_total += btor_time_stamp () - start;
  btor->last_sat_result = sat_result;
  return sat_result;
}

static void
generate_model_prop_solver (BtorPropSolver *slv,
                            bool model_for_all_nodes,
                            bool reset)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor = slv->btor;

  if (!reset && btor->bv_model) return;
  btor_init_bv_model (btor, &btor->bv_model);
  btor_init_fun_model (btor, &btor->fun_model);
  btor_generate_model (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

static void
print_stats_prop_solver (BtorPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor = slv->btor;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "restarts: %u", slv->stats.restarts);
  BTOR_MSG (btor->msg, 1, "moves: %u", slv->stats.moves);
  BTOR_MSG (btor->msg,
            1,
            "moves per second: %.2f",
            (double) slv->stats.moves / slv->time.sat);
  BTOR_MSG (btor->msg, 1, "propagation (steps): %u", slv->stats.props);
  BTOR_MSG (btor->msg,
            1,
            "propagation (steps) per second: %.2f",
            (double) slv->stats.props / slv->time.sat);
  BTOR_MSG (btor->msg, 1, "updates (cone): %u", slv->stats.updates);
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "propagation move conflicts (recoverable): %u",
            slv->stats.move_prop_rec_conf);
  BTOR_MSG (btor->msg,
            1,
            "propagation move conflicts (non-recoverable): %u",
            slv->stats.move_prop_non_rec_conf);
#ifndef NDEBUG
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (add): %u", slv->stats.cons_add);
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (and): %u", slv->stats.cons_and);
  BTOR_MSG (btor->msg, 1, "consistent fun calls (eq): %u", slv->stats.cons_eq);
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (ult): %u", slv->stats.cons_ult);
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (sll): %u", slv->stats.cons_sll);
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (srl): %u", slv->stats.cons_srl);
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (mul): %u", slv->stats.cons_mul);
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (udiv): %u", slv->stats.cons_udiv);
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (urem): %u", slv->stats.cons_urem);
  BTOR_MSG (btor->msg,
            1,
            "consistent fun calls (concat): %u",
            slv->stats.cons_concat);
  BTOR_MSG (
      btor->msg, 1, "consistent fun calls (slice): %u", slv->stats.cons_slice);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "inverse fun calls (add): %u", slv->stats.inv_add);
  BTOR_MSG (btor->msg, 1, "inverse fun calls (and): %u", slv->stats.inv_and);
  BTOR_MSG (btor->msg, 1, "inverse fun calls (eq): %u", slv->stats.inv_eq);
  BTOR_MSG (btor->msg, 1, "inverse fun calls (ult): %u", slv->stats.inv_ult);
  BTOR_MSG (btor->msg, 1, "inverse fun calls (sll): %u", slv->stats.inv_sll);
  BTOR_MSG (btor->msg, 1, "inverse fun calls (srl): %u", slv->stats.inv_srl);
  BTOR_MSG (btor->msg, 1, "inverse fun calls (mul): %u", slv->stats.inv_mul);
  BTOR_MSG (btor->msg, 1, "inverse fun calls (udiv): %u", slv->stats.inv_udiv);
  BTOR_MSG (btor->msg, 1, "inverse fun calls (urem): %u", slv->stats.inv_urem);
  BTOR_MSG (
      btor->msg, 1, "inverse fun calls (concat): %u", slv->stats.inv_concat);
  BTOR_MSG (
      btor->msg, 1, "inverse fun calls (slice): %u", slv->stats.inv_slice);
#endif
}

static void
print_time_stats_prop_solver (BtorPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor = slv->btor;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for sat call (incl. simplify)",
            slv->time.sat_total);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for sat call (excl. simplify)",
            slv->time.sat);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (total)",
            slv->time.update_cone);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (reset)",
            slv->time.update_cone_reset);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (model gen)",
            slv->time.update_cone_model_gen);
  if (btor_get_opt (btor, BTOR_OPT_PROP_USE_BANDIT))
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds for updating cone (compute score)",
              slv->time.update_cone_compute_score);
  BTOR_MSG (btor->msg, 1, "");
}

BtorSolver *
btor_new_prop_solver (Btor *btor)
{
  assert (btor);

  BtorPropSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->btor = btor;
  slv->kind = BTOR_PROP_SOLVER_KIND;

  slv->api.clone = (BtorSolverClone) clone_prop_solver;
  slv->api.delet = (BtorSolverDelete) delete_prop_solver;
  slv->api.sat   = (BtorSolverSat) sat_prop_solver;
  slv->api.generate_model =
      (BtorSolverGenerateModel) generate_model_prop_solver;
  slv->api.print_stats = (BtorSolverPrintStats) print_stats_prop_solver;
  slv->api.print_time_stats =
      (BtorSolverPrintTimeStats) print_time_stats_prop_solver;

  BTOR_MSG (btor->msg, 1, "enabled prop engine");

  return (BtorSolver *) slv;
}

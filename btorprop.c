/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
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

#include "utils/btorhash.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"

#include <math.h>

/*------------------------------------------------------------------------*/

#define BTOR_PROP_MAXSTEPS_CFACT 100
#define BTOR_PROP_MAXSTEPS(i) \
  (BTOR_PROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BTOR_PROP_SELECT_CFACT 20

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
        res = 0;
        BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
        char *sbvand = btor_bv_to_char_bv (btor->mm, bvand);
        char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := %s AND x", sbvand, sbve);
        btor_freestr (btor->mm, sbvand);
        btor_freestr (btor->mm, sbve);
#endif
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
        BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
        char *sbvult = btor_bv_to_char_bv (btor->mm, bvult);
        char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := %s < x", sbvult, sbve);
        btor_freestr (btor->mm, sbvult);
        btor_freestr (btor->mm, sbve);
#endif
      }
      else if (isult)
      {
        res = btor_new_random_range_bv (mm, &btor->rng, bw, one, bvmax);
        BTOR_INC_REC_CONF_STATS (btor, 1);
      }
      else
      {
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
        res = 0;
        BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
        char *sbvult = btor_bv_to_char_bv (btor->mm, bvult);
        char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := x < %s", sbvult, sbve);
        btor_freestr (btor->mm, sbvult);
        btor_freestr (btor->mm, sbve);
#endif
      }
      else if (!isult)
      {
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
#ifndef NDEBUG
        char *sbvsll = btor_bv_to_char_bv (btor->mm, bvsll);
        char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
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
    }

    /* check for conflict -> shifted bits must match */
    for (i = 0, j = shift; i < bve->width - j; i++)
    {
      if (btor_get_bit_bv (bve, i) != btor_get_bit_bv (bvsll, j + i))
      {
        /* check for non-recoverable conflict */
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
#ifndef NDEBUG
          char *sbvsll = btor_bv_to_char_bv (btor->mm, bvsll);
          char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
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
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
#ifndef NDEBUG
          char *sbvsll = btor_bv_to_char_bv (btor->mm, bvsll);
          char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
          BTORLOG (2, "prop CONFLICT: %s := x << %s", sbvsll, sbve);
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
#ifndef NDEBUG
        char *sbvsrl = btor_bv_to_char_bv (btor->mm, bvsrl);
        char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
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
    }

    /* check for conflict -> shifted bits must match */
    for (i = 0, j = shift; i < bve->width - j; i++)
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
          char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
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
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
#ifndef NDEBUG
          char *sbvsrl = btor_bv_to_char_bv (btor->mm, bvsrl);
          char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
          BTORLOG (2, "prop CONFLICT: %s := x >> %s", sbvsrl, sbve);
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
        BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
        char *sbvmul = btor_bv_to_char_bv (btor->mm, bvmul);
        char *sbve   = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := %s * x", sbvmul, sbve);
        btor_freestr (btor->mm, sbvmul);
        btor_freestr (btor->mm, sbve);
#endif
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

        BTOR_INC_REC_CONF_STATS (btor, 1);
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

  /* bve / e[1] = bvudiv
   *
   * -> if bvudiv = 2^bw - 1, e[1] = 0
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
      /* bvudiv = 2^bw - 1 -> e[1] = 0 */
      res = btor_new_bv (mm, bw);
    }
    else if (btor_is_zero_bv (bvudiv))
    {
      /* bvudiv = 0 and bve = 0 -> choose random e[1] > 0 */
      if (btor_is_zero_bv (bve))
        res = btor_new_random_range_bv (mm, rng, bw, one, bvmax);
      /* bvudiv = 0 and 0 < bve < 2^bw - 1 -> choose random e[1] > bve */
      else if (btor_compare_bv (bve, bvmax))
        res = btor_new_random_range_bv (mm, rng, bw, bve, bvmax);
      /* conflict */
      else
      {
      BVUDIV_E1_CONF:
        /* check for non-recoverable conflict */
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = 0;
          BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
          char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
          char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
          BTORLOG (2, "prop CONFLICT: %s := %s / x", sbvudiv, sbve);
          btor_freestr (btor->mm, sbvudiv);
          btor_freestr (btor->mm, sbve);
#endif
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
      /* if bvudiv is a divisor of bve, choose e[1] = bvudiv / bve
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
        }
      }
    }
  }

  /* e[0] / bve = bvudiv
   *
   * -> if bvudiv = 2^bw - 1 and bve = 0, choose random e[0] > 0
   *                         and bve > 0 -> conflict
   * -> if bve = 0 and bve < 2^bw - 1 -> conflict
   * -> if bve * bvudiv does not overflow, choose with 0.5 prob out of
   *      + e[0] = bve * bvudiv
   *      + choose bve s.t. e[0] / bve = bvudiv
   * -> else choose bve s.t. e[0] / bve = bvudiv  */
  else
  {
    if (!btor_compare_bv (bvudiv, bvmax))
    {
      /* bvudiv = 2^bw - 1 and bve = 0 -> choose random e[0] > 0 */
      if (btor_is_zero_bv (bve))
        res = btor_new_random_range_bv (mm, rng, bw, one, bvmax);
      /* conflict */
      else
      {
      BVUDIV_E0_CONF:
        /* check for non-recoverable conflict */
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = 0;
          BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
          char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
          char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
          BTORLOG (2, "prop CONFLICT: %s := x / %s", sbvudiv, sbve);
          btor_freestr (btor->mm, sbvudiv);
          btor_freestr (btor->mm, sbve);
#endif
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
      /* bve = 0 and bve < 2^bw - 1 -> conflict */
      goto BVUDIV_E0_CONF;
    }
    else
    {
      /* if bve * bvudiv does not overflow, choose e[0] = bve * bvudiv
       * with prob = 0.5 and a bve s.t. bve / e[1] = bvudiv otherwise */
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
           * up = (bve + 1) * bvudiv - 1 if (bve + 1) * bvudiv does
           *      not overflow else 2^bw - 1
           * lo = bve * bvudiv */
          lo  = btor_mul_bv (mm, bve, bvudiv);
          tmp = btor_inc_bv (mm, bve);
          if (btor_is_umulo_bv (mm, tmp, bvudiv))
          {
            btor_free_bv (mm, tmp);
            up = btor_copy_bv (mm, bvmax);
          }
          else
          {
            up = btor_mul_bv (mm, tmp, bvudiv);
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

#if 0
#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_udiv_bv (Btor * btor,
	     BtorNode * udiv,
	     BtorBitVector * bvudiv,
	     BtorBitVector * bve,
	     int eidx)
{
  assert (btor);
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
	  || btor->options.engine.val == BTOR_ENGINE_PROP);
  assert (BTOR_SLS_SOLVER (btor));
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);
  assert (bve->width == bvudiv->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (udiv->e[eidx])));

  int i;
  BtorNode *e;
  BtorBitVector *res, *tmp, *lo, *up, *one, *bvmax, *tmpbve;
  BtorMemMgr *mm;
#ifndef NDEBUG
  BtorBitVector *tmpdbg;
  int iscon = 0;
#endif

  mm = btor->mm;
  e = udiv->e[eidx ? 0 : 1];
  assert (e);

  one = btor_one_bv (mm, bve->width);
  bvmax = btor_ones_bv (mm, bvudiv->width);  /* 2^bw - 1 */

#if 0
  /* bve / e[1] = bvudiv 
   * -> if bvudiv is a divisor of bve, res = bve * bvudiv
   * -> else conflict */ 
  // TODO conflict case not entirely correct
  // e.g. 7 / x = 2 -> x = 7/2 = 3 which is still correct but handled as
  // conflict case here
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
	      if (btor->options.engine.val == BTOR_ENGINE_SLS 
		  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
		{
		  res = 0;
#ifndef NDEBUG
		  char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := %s / x", sbvudiv, sbve);
		  btor_freestr (btor->mm, sbvudiv);
		  btor_freestr (btor->mm, sbve);
#endif
		}
	      else
		{
		  /* e[0] = res * bvudiv s.t. res * bvudiv does not overflow */
		  res = btor_new_random_range_bv (
		      mm, &btor->rng, bve->width, one, bvmax);
		  while (btor_is_umulo_bv (mm, res, bvudiv))
		    {
		      tmp = btor_sub_bv (mm, res, one);
		      btor_free_bv (mm, res);
		      res = btor_new_random_range_bv (
			  mm, &btor->rng, bve->width, one, tmp);
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
	      if (btor->options.engine.val == BTOR_ENGINE_SLS 
		  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
		{
		  res = 0;
#ifndef NDEBUG
		  char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := %s / x", sbvudiv, sbve);
		  btor_freestr (btor->mm, sbvudiv);
		  btor_freestr (btor->mm, sbve);
#endif
		}
	      else
		{
		  tmp = btor_copy_bv (mm, bvmax);
		  res = btor_new_random_range_bv (
		      mm, &btor->rng, bve->width, one, tmp);

		  while (btor_is_umulo_bv (mm, res, bvudiv))
		    {
		      btor_free_bv (mm, tmp);
		      tmp = btor_sub_bv (mm, res, one);
		      btor_free_bv (mm, res);
		      res = btor_new_random_range_bv (
			  mm, &btor->rng, bve->width, one, tmp);
		    }

		  btor_free_bv (mm, tmp);

		  BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
		}
	    }
	}
    }
#endif
  /* bve / e[1] = bvudiv 
   * -> if bvudiv = 2^bw - 1, x = 0
   * -> if bve = 0 and bvudiv = 0, choose random value for e[1] 
   *           |-> and bvudiv < 2^bw - 1 -> conflict 
   * -> if bve < bvudiv -> conflict
   * -> else choose e[1] s.t. bve / e[1] = bvudiv */
  if (eidx)
    {
      tmpbve = 0;

      if (!btor_compare_bv (bvudiv, bvmax))
	{
	  /* bve / e[1] = 2^bw - 1  ->  e[1] = 0 */
	  res = btor_new_bv (mm, bve->width);
	}
      else if (btor_is_zero_bv (bve))
	{
	  /* if bvudiv = 0, choose random non-zero e[1], else conflict */
	  if (btor_is_zero_bv (bvudiv))
	    {
	      res = btor_new_random_range_bv (
		  mm, &btor->rng, bve->width, one, bvmax);
	    }
	  else  /* conflict */
	    {
#ifndef NDEBUG
	      iscon = 1;
#endif
BVUDIV_E1_CONF:
	      /* check for non-recoverable conflict */
	      if (btor->options.engine.val == BTOR_ENGINE_SLS 
		  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
		{
		  res = 0;
#ifndef NDEBUG
		  char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := %s / x", sbvudiv, sbve);
		  btor_freestr (btor->mm, sbvudiv);
		  btor_freestr (btor->mm, sbve);
#endif
		}
	      else
		{
		  /* disregard bve, choose random bve and e[1] such that 
		   * bve / e[1] = bvudiv (max. 5 tries) */
		  for (i = 0, res = 0; i < 5; i++)
		    {
		      tmpbve = btor_new_random_range_bv (
			  mm, &btor->rng, bve->width, bvudiv, bvmax);
		      /* upper bound
		       * up = bve / bvudiv */
		      up = btor_udiv_bv (mm, tmpbve, bvudiv);
		      /* lower bound
		       * lo = bve / (bvudiv + 1) + 1 */
		      tmp = btor_inc_bv (mm, bvudiv);
		      lo = btor_udiv_bv (mm, tmpbve, tmp);
		      btor_free_bv (mm, tmp);
		      tmp = lo;
		      lo = btor_inc_bv (mm, tmp);

		      if (btor_compare_bv (lo, up) <= 0)
			{
			  res = btor_new_random_range_bv (
			    mm, &btor->rng, bve->width, lo, up);
			  btor_free_bv (mm, tmpbve);
			  break;
			}
		      /* else: again, conflict */
		      btor_free_bv (mm, tmpbve);
		    }
		}
	    }
	}
      /* bve < bvudiv -> conflict */
      else if (btor_compare_bv (bve, bvudiv) < 0)
	{
#ifndef NDEBUG
	  iscon = 1;
#endif
	  goto BVUDIV_E1_CONF;
	}
      else
	{
	  /* Choose e[1] out of all options that yield bve / e[1] = bvudiv 
	   * Note: udiv always truncates the result towards 0. */

	  /* determine upper and lower bounds for e[1]:
	   * upper: bve / bvudiv
	   * lower: bve / (bvudiv +1) + 1 
	   * if lower > upper -> conflict */
	  up = btor_udiv_bv (mm, bve, bvudiv);  /* upper bound */
	  tmp = btor_inc_bv (mm, bvudiv);
	  lo = btor_udiv_bv (mm, bve, tmp);     /* lower bound (excl.) */
	  btor_free_bv (mm, tmp);
	  tmp = lo;
	  lo = btor_inc_bv (mm, tmp);           /* lower bound (incl.) */
	  
	  /* lo > up -> conflict */
	  if (btor_compare_bv (lo, up) > 0)
	    {
#ifndef NDEBUG
	      iscon = 1;
#endif
	      btor_free_bv (mm, lo);
	      btor_free_bv (mm, up);
	      goto BVUDIV_E1_CONF;
	    }
	  /* choose lo <= e[1] <= up */
	  else
	    {
	      /* choose division with remainder 0 or
	       * randomly pick one of the candidates from lo to up
	       * with 0.5 probability */
	      if (btor_pick_rand_rng (&btor->rng, 0, 1))
		res = btor_copy_bv (mm, up);
	      else
		res = btor_new_random_range_bv (
		    mm, &btor->rng, bve->width, lo, up);
	    }

	  btor_free_bv (mm, lo);
	  btor_free_bv (mm, up);
	}
    }

#if 0
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
	      if (btor->options.engine.val == BTOR_ENGINE_SLS 
		  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
		{
		  res = 0;
#ifndef NDEBUG
		  char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := x / %s", sbvudiv, sbve);
		  btor_freestr (btor->mm, sbvudiv);
		  btor_freestr (btor->mm, sbve);
#endif
		}
	      else
		{
		  /* res = n * bvudiv s.t. n * bvudiv does not overflow */
		  n = btor_new_random_range_bv (
		      mm, &btor->rng, bve->width, one, bvmax);
		  while (btor_is_umulo_bv (mm, n, bvudiv))
		    {
		      tmp = btor_sub_bv (mm, n, one);
		      btor_free_bv (mm, n);
		      n = btor_new_random_range_bv (
			  mm, &btor->rng, bve->width, one, tmp);
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
	      if (btor->options.engine.val == BTOR_ENGINE_SLS 
		  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
		{
		  res = 0;
#ifndef NDEBUG
		  char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := x / %s", sbvudiv, sbve);
		  btor_freestr (btor->mm, sbvudiv);
		  btor_freestr (btor->mm, sbve);
#endif
		}
	      else
		{
		  tmp = btor_sub_bv (mm, bve, one);
		  res = btor_new_random_range_bv (
		      mm, &btor->rng, bve->width, one, tmp);

		  while (btor_is_umulo_bv (mm, res, bvudiv))
		    {
		      btor_free_bv (mm, tmp);
		      tmp = btor_sub_bv (mm, res, one);
		      btor_free_bv (mm, res);
		      res = btor_new_random_range_bv (
			  mm, &btor->rng, bve->width, one, tmp);
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
#endif

  /* e[0] / bve = bvudiv
   * -> if bve = 0 and bvudiv = 1...1, choose e[0] randomly
   * -> if bve = 0 and bvudiv < 1...1 -> conflict
   * -> if bve * bvudiv does not overflow, choose e[0] s.t. e[0] / bve = bvudiv
   * -> else conflict */
  else
    {
      if (btor_is_zero_bv (bve))
	{
	  /* e[0] / 0 ) 1...1, else conflict */
	  if (!btor_compare_bv (bvmax, bvudiv))
	    res = btor_new_random_bv (mm, &btor->rng, bve->width);
	  else
	    {
#ifndef NDEBUG
	      iscon = 1;
#endif
BVUDIV_E0_CONF:
	      /* check for non-recoverable conflict */
	      if (btor->options.engine.val == BTOR_ENGINE_SLS 
		  && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
		{
		  res = 0;
#ifndef NDEBUG
		  char *sbvudiv = btor_bv_to_char_bv (btor->mm, bvudiv);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := x / %s", sbvudiv, sbve);
		  btor_freestr (btor->mm, sbvudiv);
		  btor_freestr (btor->mm, sbve);
#endif
		}
	      else
		{
		  /* choose bve s.t. bve * bvudiv does not overflow,
		   * then choose e[0] s.t e[0] / bve = bvudiv */
		  tmpbve = btor_new_random_range_bv (
		      mm, &btor->rng, bve->width, one, bvmax);
		  while (btor_is_umulo_bv (mm, tmpbve, bvudiv))
		    {
		      tmp = btor_sub_bv (mm, tmpbve, one);
		      btor_free_bv (mm, tmpbve);
		      tmpbve = btor_new_random_range_bv (
			  mm, &btor->rng, bve->width, one, tmp);
		      btor_free_bv (mm, tmp);
		    }

		  /* lower bound 
		   * lo = bve * bvudiv */
		  lo = btor_mul_bv (mm, tmpbve, bvudiv);
		  /* upper bound
		   * up = (bve + 1) * bvudiv - 1 if (bve + 1) * bvudiv
		   * does not overflow, else 2^bw - 1 */
		  tmp = btor_inc_bv (mm, tmpbve);
		  if (btor_is_umulo_bv (mm, tmp, bvudiv))
		    {
		      btor_free_bv (mm, tmp);
		      up = btor_copy_bv (mm, bvmax);
		    }
		  else
		    {
		      up = btor_mul_bv (mm, tmp, bvudiv);
		      btor_free_bv (mm, tmp);
		      tmp = btor_dec_bv (mm, up);
		      btor_free_bv (mm, up);
		      up = tmp;
		    }

		  /* choose division with remainder 0 or
		   * randomly pick one of the candidates from lo to up
		   * with 0.5 probability */
		  if (btor_pick_rand_rng (&btor->rng, 0, 1))
		    res = btor_copy_bv (mm, lo);
		  else
		    res = btor_new_random_range_bv (
			mm, &btor->rng, bve->width, lo, up);

		  btor_free_bv (mm, tmpbve);
		  btor_free_bv (mm, up);
		  btor_free_bv (mm, lo);

		  BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
		}
	    }
	}
      else
	{
	  if (btor_is_umulo_bv (mm, bve, bvudiv))
	    {
#ifndef NDEBUG
	      iscon = 1;
#endif
	      goto BVUDIV_E0_CONF;
	    }
	  else
	    {
	      /* lower bound 
	       * lo = bve * bvudiv */
	      lo = btor_mul_bv (mm, bve, bvudiv);
	      /* upper bound
	       * up = (bve + 1) * bvudiv - 1 if (bve + 1) * bvudiv
	       * does not overflow, else 2^bw - 1 */
	      tmp = btor_inc_bv (mm, bve);
	      if (btor_is_umulo_bv (mm, tmp, bvudiv))
		{
		  btor_free_bv (mm, tmp);
		  up = btor_copy_bv (mm, bvmax);
		}
	      else
		{
		  up = btor_mul_bv (mm, tmp, bvudiv);
		  btor_free_bv (mm, tmp);
		  tmp = btor_dec_bv (mm, up);
		  btor_free_bv (mm, up);
		  up = tmp;
		}
	      
	      res = btor_new_random_range_bv (
		  mm, &btor->rng, bve->width, lo, up);

	      btor_free_bv (mm, up);
	      btor_free_bv (mm, lo);
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
      char *sbve = btor_bv_to_char_bv (btor->mm, bve);
      char *sres = btor_bv_to_char_bv (btor->mm, res);
      if (eidx)
	BTORLOG (3, "prop (e[%d]): %s: %s := %s * %s",
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
#endif

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
      RES_GT_BVUREM_CONF:
        res = 0;
        BTOR_INC_NON_REC_CONF_STATS (btor, 1);
#ifndef NDEBUG
        char *sbvurem = btor_bv_to_char_bv (btor->mm, bvurem);
        char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := %s %% x", sbvurem, sbve);
        btor_freestr (btor->mm, sbvurem);
        btor_freestr (btor->mm, sbve);

        iscon = 1;
#endif

// TODO doesn't make a difference if this case produces a randomized
// result or no result at all
#if 0
RES_GT_BVUREM_CONF:
	      if (btor->options.engine.val == BTOR_ENGINE_SLS)
		{
		  assert (btor->options.engine.val == BTOR_ENGINE_SLS);
		  res = 0;
		  BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
		  char *sbvurem = btor_bv_to_char_bv (btor->mm, bvurem);
		  char *sbve = btor_bv_to_char_bv (btor->mm, bve);
		  BTORLOG (2, "prop CONFLICT: %s := %s %% x", sbvurem, sbve);
		  btor_freestr (btor->mm, sbvurem);
		  btor_freestr (btor->mm, sbve);
#endif
		}
	      else
		{
		  res = btor_new_random_bv (btor->mm, &btor->rng, bve->width);
		  BTOR_INC_REC_CONF_STATS (btor, 1);
		}
#ifndef NDEBUG
		  iscon = 1;
#endif
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
        if (btor->options.engine.val == BTOR_ENGINE_SLS
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
        {
          res = 0;
          BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
          char *sbvurem = btor_bv_to_char_bv (btor->mm, bvurem);
          char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
          BTORLOG (2, "prop CONFLICT: %s := %s %% x", sbvurem, sbve);
          btor_freestr (btor->mm, sbvurem);
          btor_freestr (btor->mm, sbve);
#endif
        }
        else
        {
          BTOR_INC_REC_CONF_STATS (btor, 1);
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
        BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
        char *sbvurem = btor_bv_to_char_bv (btor->mm, bvurem);
        char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := %s %% x", sbvurem, sbve);
        btor_freestr (btor->mm, sbvurem);
        btor_freestr (btor->mm, sbve);
#endif
      }
      /* still non-recoverable if bvurem = 2^bw - 1 */
      else if (!btor_compare_bv (bvurem, bvmax))
      {
        goto RES_GT_BVUREM_CONF;
      }
      else
      {
        BTOR_INC_REC_CONF_STATS (btor, 1);
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
          if (btor->options.engine.val == BTOR_ENGINE_SLS
              && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
          {
            res = 0;
            BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
            char *sbvurem = btor_bv_to_char_bv (btor->mm, bvurem);
            char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
            BTORLOG (2, "prop CONFLICT: %s := x %% %s", sbvurem, sbve);
            btor_freestr (btor->mm, sbvurem);
            btor_freestr (btor->mm, sbve);
#endif
          }
          else
          {
            BTOR_INC_REC_CONF_STATS (btor, 1);
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
      if (btor->options.engine.val == BTOR_ENGINE_SLS
          && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e)))
      {
        res = 0;
        BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
        char *sbvurem = btor_bv_to_char_bv (btor->mm, bvurem);
        char *sbve    = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := x %% %s", sbvurem, sbve);
        btor_freestr (btor->mm, sbvurem);
        btor_freestr (btor->mm, sbve);
#endif
      }
      else
      {
        BTOR_INC_REC_CONF_STATS (btor, 1);
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
        res = 0;
        BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
        char *sbvconcat = btor_bv_to_char_bv (btor->mm, bvconcat);
        char *sbve      = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := %s o x", sbvconcat, sbve);
        btor_freestr (btor->mm, sbvconcat);
        btor_freestr (btor->mm, sbve);
#endif
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
        res = 0;
        BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
#ifndef NDEBUG
        char *sbvconcat = btor_bv_to_char_bv (btor->mm, bvconcat);
        char *sbve      = btor_bv_to_char_bv (btor->mm, bve);
        BTORLOG (2, "prop CONFLICT: %s := x o %s", sbvconcat, sbve);
        btor_freestr (btor->mm, sbvconcat);
        btor_freestr (btor->mm, sbve);
#endif
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
inv_slice_bv (Btor *btor, BtorNode *slice, BtorBitVector *bvslice)
{
  assert (btor);
  assert (btor->options.engine.val == BTOR_ENGINE_SLS
          || btor->options.engine.val == BTOR_ENGINE_PROP);
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

void
btor_select_prop_move (Btor *btor,
                       BtorNode *root,
                       BtorNode **input,
                       BtorBitVector **assignment)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (root);
  assert (
      btor_bv_to_uint64_bv ((BtorBitVector *) btor_get_bv_model (btor, root))
      == 0);

  int i, eidx, idx;
  BtorNode *cur, *real_cur;
  BtorBitVector *bve[3], *bvcur, *bvenew, *tmp;

  *input      = 0;
  *assignment = 0;

  cur   = root;
  bvcur = btor_one_bv (btor->mm, 1);

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
      // TODO how to handle this in the engine=prop case?
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

    /* found input and assignment */
    if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[eidx])))
    {
      cur = real_cur->e[eidx];
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
      cur      = real_cur->e[eidx];
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
    else
      cur = real_cur->e[eidx];

    btor_free_bv (btor->mm, bvcur);
    bvcur = bvenew;
  }
  btor_free_bv (btor->mm, bvcur);
}

/*------------------------------------------------------------------------*/

// TODO currently both reset_cone and update_cone do almost exactly the
// same as their sls counter parts, if this does not change (e.g. if
// using a score is not eliminated) the functions in sls and prop should
// be merged
static void
reset_cone (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (exp);

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
  assert (score);

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
  btor_compute_sls_scores (btor, BTOR_PROP_SOLVER (btor)->score);
}

static BtorNode *
select_constraint (Btor *btor, int nmoves)
{
  assert (btor);

  int *selected;
  double value, max_value, score;
  BtorNode *res, *cur;
  BtorPropSolver *slv;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;

  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  assert (slv->roots);
  assert (slv->score);

  res       = 0;
  max_value = 0.0;
  btor_init_hash_table_iterator (&it, slv->roots);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    selected = &it.bucket->data.asInt;
    cur      = btor_next_node_hash_table_iterator (&it);
    b        = btor_find_in_ptr_hash_table (slv->score, cur);
    assert (b);
    if ((score = b->data.asDbl) >= 1.0) continue;
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

  assert (res);

  BTORLOG (1, "");
  BTORLOG (1, "*** select constraint: %s", node2string (res));

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

static void
move (Btor *btor, int nmoves)
{
  assert (btor);
  assert (!all_constraints_sat (btor));

  BTORLOG (1, "");
  BTORLOG (1, "*** move");

  BtorNode *root, *input;
  BtorBitVector *assignment;

  root = select_constraint (btor, nmoves);

  do
  {
    btor_select_prop_move (btor, root, &input, &assignment);
  } while (!input);

#ifndef NBTORLOG
  char *a;
  BtorBitVector *ass;
  ass = (BtorBitVector *) btor_get_bv_model (btor, input);
  a   = btor_bv_to_char_bv (btor->mm, ass);
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

/* Note: failed assumptions -> no handling necessary, prop only works for SAT
 * Note: limits are currently unused */
static int
sat_prop_solver (Btor *btor, int limit0, int limit1)
{
  assert (btor);

  int j, max_steps;
  int sat_result;
  int nmoves;
  BtorHashTableIterator it;
  BtorPropSolver *slv;

  (void) limit0;
  (void) limit1;

  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);

  nmoves = 0;

  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_UNKNOWN;
    goto DONE;
  }

  sat_result = btor_simplify (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->ufs->count != 0
          || (!btor->options.beta_reduce_all.val && btor->lambdas->count != 0),
      "prop engine supports QF_BV only");
  btor_update_assumptions (btor);

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
    btor_insert_in_ptr_hash_table (slv->roots,
                                   btor_next_node_hash_table_iterator (&it));

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
    btor_compute_sls_scores (btor, slv->score);

    if (all_constraints_sat (btor))
    {
      sat_result = BTOR_SAT;
      goto SAT;
    }

    for (j = 0, max_steps = BTOR_PROP_MAXSTEPS (slv->stats.restarts + 1);
         j < max_steps;
         j++)
    {
      if (btor_terminate_btor (btor))
      {
        sat_result = BTOR_UNKNOWN;
        goto DONE;
      }

      move (btor, nmoves++);

      if (all_constraints_sat (btor))
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
  assert (slv->stats.moves == nmoves);
  goto DONE;

UNSAT:
  sat_result = BTOR_UNSAT;

DONE:
  if (slv->roots)
  {
    btor_init_node_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_node_hash_table_iterator (&it))
      BTOR_DELETE (
          btor->mm,
          (BtorSLSConstrData *) btor_next_data_node_hash_table_iterator (&it)
              ->asPtr);
    btor_delete_ptr_hash_table (slv->roots);
    slv->roots = 0;
  }
  btor->last_sat_result = sat_result;
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
  (void) btor;
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

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testpropinv.h"
#include "btorbv.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btornode.h"
#include "btorslvpropsls.h"
#include "testrunner.h"
#include "utils/btorutil.h"

static Btor *g_btor;
static BtorMemMgr *g_mm;
static BtorRNG *g_rng;

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#define TEST_PROP_INV_COMPLETE_BW 8
#define TEST_PROP_INV_COMPLETE_N_TESTS 10000

#define TEST_PROP_INV_COMPLETE_BINARY_INIT(expfun) \
  do                                               \
  {                                                \
    bw   = TEST_PROP_INV_COMPLETE_BW;              \
    sort = btor_sort_bv (g_btor, bw);          \
    e[0] = btor_exp_var (g_btor, sort, 0);         \
    e[1] = btor_exp_var (g_btor, sort, 0);         \
    btor_sort_release (g_btor, sort);              \
    exp = expfun (g_btor, e[0], e[1]);             \
  } while (0)

#define TEST_PROP_INV_COMPLETE_SHIFT_INIT(expfun) \
  do                                              \
  {                                               \
    bw   = TEST_PROP_INV_COMPLETE_BW;             \
    sbw  = btor_util_log_2 (bw);                  \
    sort = btor_sort_bv (g_btor, bw);         \
    e[0] = btor_exp_var (g_btor, sort, 0);        \
    btor_sort_release (g_btor, sort);             \
    sort = btor_sort_bv (g_btor, sbw);        \
    e[1] = btor_exp_var (g_btor, sort, 0);        \
    btor_sort_release (g_btor, sort);             \
    exp = expfun (g_btor, e[0], e[1]);            \
  } while (0)

#define TEST_PROP_INV_COMPLETE_BINARY_FINISH(fun) \
  do                                              \
  {                                               \
    btor_node_release (g_btor, e[0]);             \
    btor_node_release (g_btor, e[1]);             \
    btor_node_release (g_btor, exp);              \
  } while (0)

#define TEST_PROP_INV_COMPLETE_EIDX(fun, bve, bvn, bvres, eidx)   \
  do                                                              \
  {                                                               \
    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++) \
    {                                                             \
      res = inv_##fun##_bv (g_btor, exp, bvn, bve, eidx);         \
      assert (res);                                               \
      if (!btor_bv_compare (res, bvres)) break;                   \
      btor_bv_free (g_mm, res);                                   \
      res = 0;                                                    \
    }                                                             \
    assert (res);                                                 \
    assert (!btor_bv_compare (res, bvres));                       \
    btor_bv_free (g_mm, res);                                     \
  } while (0)

#define TEST_PROP_INV_COMPLETE_BINARY(fun, expfun)                   \
  do                                                                 \
  {                                                                  \
    uint32_t bw;                                                     \
    uint64_t i, j, k;                                                \
    BtorNode *exp, *e[2];                                            \
    BtorSortId sort;                                                 \
    BtorBitVector *bve[2], *bvexp, *res;                             \
    TEST_PROP_INV_COMPLETE_BINARY_INIT (expfun);                     \
    for (i = 0; i < (uint32_t) (1 << bw); i++)                       \
    {                                                                \
      bve[0] = btor_bv_uint64_to_bv (g_mm, i, bw);                   \
      for (j = 0; j < (uint32_t) (1 << bw); j++)                     \
      {                                                              \
        bve[1] = btor_bv_uint64_to_bv (g_mm, j, bw);                 \
        bvexp  = btor_bv_##fun (g_mm, bve[0], bve[1]);               \
        TEST_PROP_INV_COMPLETE_EIDX (fun, bve[0], bvexp, bve[1], 1); \
        TEST_PROP_INV_COMPLETE_EIDX (fun, bve[1], bvexp, bve[0], 0); \
        btor_bv_free (g_mm, bve[1]);                                 \
        btor_bv_free (g_mm, bvexp);                                  \
      }                                                              \
      btor_bv_free (g_mm, bve[0]);                                   \
    }                                                                \
    TEST_PROP_INV_COMPLETE_BINARY_FINISH (fun);                      \
  } while (0)

#define TEST_PROP_INV_COMPLETE_SHIFT(fun, expfun)                    \
  do                                                                 \
  {                                                                  \
    uint32_t bw, sbw;                                                \
    uint64_t i, j, k;                                                \
    BtorNode *exp, *e[2];                                            \
    BtorSortId sort;                                                 \
    BtorBitVector *bve[2], *bvexp, *res;                             \
    TEST_PROP_INV_COMPLETE_SHIFT_INIT (expfun);                      \
    for (i = 0; i < (uint32_t) (1 << bw); i++)                       \
    {                                                                \
      bve[0] = btor_bv_uint64_to_bv (g_mm, i, bw);                   \
      for (j = 0; j < (uint32_t) (1 << sbw); j++)                    \
      {                                                              \
        bve[1] = btor_bv_uint64_to_bv (g_mm, j, sbw);                \
        bvexp  = btor_bv_##fun (g_mm, bve[0], bve[1]);               \
        TEST_PROP_INV_COMPLETE_EIDX (fun, bve[0], bvexp, bve[1], 1); \
        TEST_PROP_INV_COMPLETE_EIDX (fun, bve[1], bvexp, bve[0], 0); \
        btor_bv_free (g_mm, bve[1]);                                 \
        btor_bv_free (g_mm, bvexp);                                  \
      }                                                              \
      btor_bv_free (g_mm, bve[0]);                                   \
    }                                                                \
    TEST_PROP_INV_COMPLETE_BINARY_FINISH (fun);                      \
  } while (0)
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static void
test_propinv_complete_add_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_BINARY (add, btor_exp_bv_add);
#endif
}

static void
test_propinv_complete_and_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_BINARY (and, btor_exp_bv_and);
#endif
}

static void
test_propinv_complete_eq_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_BINARY (eq, btor_exp_eq);
#endif
}

static void
test_propinv_complete_ult_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_BINARY (ult, btor_exp_bv_ult);
#endif
}

static void
test_propinv_complete_sll_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_SHIFT (sll, btor_exp_bv_sll);
#endif
}

static void
test_propinv_complete_srl_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_SHIFT (srl, btor_exp_bv_srl);
#endif
}

static void
test_propinv_complete_mul_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_BINARY (mul, btor_exp_bv_mul);
#endif
}

static void
test_propinv_complete_udiv_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_BINARY (udiv, btor_exp_bv_udiv);
#endif
}

static void
test_propinv_complete_urem_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_BINARY (urem, btor_exp_bv_urem);
#endif
}

static void
test_propinv_complete_concat_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_INV_COMPLETE_BINARY (concat, btor_exp_bv_concat);
#endif
}

static void
test_propinv_complete_slice_bv (void)
{
#ifndef NDEBUG
  uint32_t bw;
  uint64_t up, lo, i, k;
  BtorNode *exp, *e;
  BtorBitVector *bve, *bvexp, *res;
  BtorSortId sort;

  bw   = TEST_PROP_INV_COMPLETE_BW;
  sort = btor_sort_bv (g_btor, bw);
  e    = btor_exp_var (g_btor, sort, 0);
  btor_sort_release (g_btor, sort);

  for (lo = 0; lo < bw; lo++)
  {
    for (up = lo; up < bw; up++)
    {
      exp = btor_exp_bv_slice (g_btor, e, up, lo);
      for (i = 0; i < (uint32_t) (1 << bw); i++)
      {
        bve   = btor_bv_uint64_to_bv (g_mm, i, bw);
        bvexp = btor_bv_slice (g_mm, bve, up, lo);
        for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
        {
          res = inv_slice_bv (g_btor, exp, bvexp, bve, 0);
          assert (res);
          if (!btor_bv_compare (res, bve)) break;
          btor_bv_free (g_mm, res);
          res = 0;
        }
        assert (res);
        assert (!btor_bv_compare (res, bve));
        btor_bv_free (g_mm, res);
        btor_bv_free (g_mm, bvexp);
        btor_bv_free (g_mm, bve);
      }
      btor_node_release (g_btor, exp);
    }
  }
  btor_node_release (g_btor, e);
#endif
}

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#define TEST_PROP_INV_CONF_BINARY_INIT(fun, expfun) \
  do                                                \
  {                                                 \
    sort = btor_sort_bv (g_btor, bw);           \
    e[0] = btor_exp_var (g_btor, sort, 0);          \
    e[1] = btor_exp_var (g_btor, sort, 0);          \
    btor_sort_release (g_btor, sort);               \
    fun = expfun (g_btor, e[0], e[1]);              \
  } while (0)

#define TEST_PROP_INV_CONF_SHIFT_INIT(fun, expfun)          \
  do                                                        \
  {                                                         \
    sort = btor_sort_bv (g_btor, bw);                   \
    e[0] = btor_exp_var (g_btor, sort, 0);                  \
    btor_sort_release (g_btor, sort);                       \
    sort = btor_sort_bv (g_btor, btor_util_log_2 (bw)); \
    e[1] = btor_exp_var (g_btor, sort, 0);                  \
    btor_sort_release (g_btor, sort);                       \
    fun = expfun (g_btor, e[0], e[1]);                      \
  } while (0)

#define TEST_PROP_INV_CONF_BINARY_FINISH(fun) \
  do                                          \
  {                                           \
    btor_node_release (g_btor, fun);          \
    btor_node_release (g_btor, e[0]);         \
    btor_node_release (g_btor, e[1]);         \
  } while (0)

#define TEST_PROP_INV_CONF_SHIFT(eidx, fun, expfun, ve, vshift, rvalmax) \
  do                                                                     \
  {                                                                      \
    bve     = btor_bv_char_to_bv (g_mm, ve);                             \
    bv##fun = btor_bv_char_to_bv (g_mm, vshift);                         \
    ce      = btor_exp_bv_const (g_btor, bve);                              \
    if (eidx)                                                            \
    {                                                                    \
      c##fun = expfun (g_btor, ce, e[1]);                                \
      res    = inv_##fun##_bv (g_btor, fun, bv##fun, bve, 1);            \
      assert (res);                                                      \
      assert (btor_bv_to_uint64 (res) <= rvalmax);                       \
      btor_bv_free (g_mm, res);                                          \
      res = inv_##fun##_bv (g_btor, c##fun, bv##fun, bve, 1);            \
      if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)     \
      {                                                                  \
        assert (!res);                                                   \
      }                                                                  \
      else                                                               \
      {                                                                  \
        assert (res);                                                    \
        assert (btor_bv_to_uint64 (res) <= rvalmax);                     \
        btor_bv_free (g_mm, res);                                        \
      }                                                                  \
    }                                                                    \
    else                                                                 \
    {                                                                    \
      c##fun = expfun (g_btor, e[0], ce);                                \
      res    = inv_##fun##_bv (g_btor, fun, bv##fun, bve, 0);            \
      assert (res);                                                      \
      btor_bv_free (g_mm, res);                                          \
      res = inv_##fun##_bv (g_btor, c##fun, bv##fun, bve, 0);            \
      if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)     \
      {                                                                  \
        assert (!res);                                                   \
      }                                                                  \
      else                                                               \
      {                                                                  \
        assert (res);                                                    \
        btor_bv_free (g_mm, res);                                        \
      }                                                                  \
    }                                                                    \
    btor_bv_free (g_mm, bv##fun);                                        \
    btor_bv_free (g_mm, bve);                                            \
    btor_node_release (g_btor, ce);                                      \
    btor_node_release (g_btor, c##fun);                                  \
  } while (0)

#define TEST_PROP_INV_CONF_MUL(cinit)                                       \
  do                                                                        \
  {                                                                         \
    if (cinit)                                                              \
    {                                                                       \
      ce[0]   = btor_exp_bv_const (g_btor, bve);                               \
      ce[1]   = btor_exp_bv_const (g_btor, bve);                               \
      cmul[0] = btor_exp_bv_mul (g_btor, ce[0], e[1]);                      \
      cmul[1] = btor_exp_bv_mul (g_btor, e[0], ce[1]);                      \
    }                                                                       \
    res = inv_mul_bv (g_btor, mul, bvmul, bve, 0);                          \
    assert (res);                                                           \
    btor_bv_free (g_mm, res);                                               \
    res = inv_mul_bv (g_btor, mul, bvmul, bve, 1);                          \
    assert (res);                                                           \
    btor_bv_free (g_mm, res);                                               \
    res = inv_mul_bv (g_btor, cmul[1], bvmul, bve, 0);                      \
    assert (                                                                \
        (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS && !res) \
        || (btor_opt_get (g_btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_SLS       \
            && res));                                                       \
    if (res)                                                                \
    {                                                                       \
      if (btor_bv_get_bit (bvmul, 0)) assert (btor_bv_get_bit (res, 0));    \
      btor_bv_free (g_mm, res);                                             \
    }                                                                       \
    res = inv_mul_bv (g_btor, cmul[0], bvmul, bve, 1);                      \
    assert (                                                                \
        (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS && !res) \
        || (btor_opt_get (g_btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_SLS       \
            && res));                                                       \
    if (res)                                                                \
    {                                                                       \
      if (btor_bv_get_bit (bvmul, 0)) assert (btor_bv_get_bit (res, 0));    \
      btor_bv_free (g_mm, res);                                             \
    }                                                                       \
    if (cinit)                                                              \
    {                                                                       \
      btor_node_release (g_btor, ce[0]);                                    \
      btor_node_release (g_btor, ce[1]);                                    \
      btor_node_release (g_btor, cmul[0]);                                  \
      btor_node_release (g_btor, cmul[1]);                                  \
    }                                                                       \
  } while (0)

#define TEST_PROP_INV_CONF_UDIV(eidx)                                         \
  do                                                                          \
  {                                                                           \
    if (eidx)                                                                 \
    {                                                                         \
      ce    = btor_exp_bv_const (g_btor, bve);                                   \
      cudiv = btor_exp_bv_udiv (g_btor, ce, e[1]);                            \
      res   = inv_udiv_bv (g_btor, udiv, bvudiv, bve, 1);                     \
      assert (res);                                                           \
      assert (!btor_bv_is_umulo (g_mm, res, bvudiv));                         \
      btor_bv_free (g_mm, res);                                               \
      res = inv_udiv_bv (g_btor, cudiv, bvudiv, bve, 1);                      \
      if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)          \
        assert (!res);                                                        \
      else                                                                    \
      {                                                                       \
        assert (res);                                                         \
        assert (!btor_bv_is_umulo (g_mm, res, bvudiv));                       \
        btor_bv_free (g_mm, res);                                             \
      }                                                                       \
      btor_node_release (g_btor, cudiv);                                      \
      btor_node_release (g_btor, ce);                                         \
    }                                                                         \
    else                                                                      \
    {                                                                         \
      ce    = btor_exp_bv_const (g_btor, bve);                                   \
      cudiv = btor_exp_bv_udiv (g_btor, e[0], ce);                            \
      res   = inv_udiv_bv (g_btor, udiv, bvudiv, bve, 0);                     \
      assert (res);                                                           \
      btor_bv_free (g_mm, res);                                               \
      res = inv_udiv_bv (g_btor, cudiv, bvudiv, bve, 0);                      \
      assert (                                                                \
          (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS && !res) \
          || (btor_opt_get (g_btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_SLS       \
              && res));                                                       \
      if (res) btor_bv_free (g_mm, res);                                      \
      btor_node_release (g_btor, cudiv);                                      \
      btor_node_release (g_btor, ce);                                         \
    }                                                                         \
  } while (0)

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static void
prop_inv_conf_and_bv (uint32_t bw)
{
  (void) bw;
#ifndef NDEBUG
  uint64_t i, j;
  BtorNode *and, *cand[2], *e[2], *ce[2];
  BtorSortId sort;
  BtorBitVector *bvand, *bve[2], *res, *tmp, *tmp2;
  BtorSolver *slv = 0;

  TEST_PROP_INV_CONF_BINARY_INIT (and, btor_exp_bv_and);

  for (i = 0; i < (uint32_t) (1 << bw); i++)
  {
    bve[0]  = btor_bv_uint64_to_bv (g_mm, i, bw);
    bve[1]  = btor_bv_uint64_to_bv (g_mm, i, bw);
    ce[0]   = btor_exp_bv_const (g_btor, bve[0]);
    ce[1]   = btor_exp_bv_const (g_btor, bve[1]);
    cand[0] = btor_exp_bv_and (g_btor, ce[0], e[1]);
    cand[1] = btor_exp_bv_and (g_btor, e[0], ce[1]);

    for (j = 0; j < (uint32_t) (1 << bw); j++)
    {
      bvand = btor_bv_uint64_to_bv (g_mm, j, bw);
      tmp   = btor_bv_and (g_mm, bve[0], bvand);
      if (btor_bv_compare (tmp, bvand))
      {
      PROP_INV_CONF_AND_TESTS:
        /* prop engine: all conflicts are treated as fixable */
        res = inv_and_bv (g_btor, and, bvand, bve[1], 0);
        assert (res);
        tmp2 = btor_bv_and (g_mm, bvand, res);
        assert (!btor_bv_compare (tmp2, bvand));
        btor_bv_free (g_mm, res);
        btor_bv_free (g_mm, tmp2);

        res = inv_and_bv (g_btor, and, bvand, bve[0], 1);
        assert (res);
        tmp2 = btor_bv_and (g_mm, bvand, res);
        assert (!btor_bv_compare (tmp2, bvand));
        btor_bv_free (g_mm, res);
        btor_bv_free (g_mm, tmp2);

        res = inv_and_bv (g_btor, cand[0], bvand, bve[0], 1);
        if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
          assert (!res);
        else
        {
          assert (res);
          tmp2 = btor_bv_and (g_mm, bvand, res);
          assert (!btor_bv_compare (tmp2, bvand));
          btor_bv_free (g_mm, res);
          btor_bv_free (g_mm, tmp2);
        }

        res = inv_and_bv (g_btor, cand[1], bvand, bve[1], 0);
        if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
          assert (!res);
        else
        {
          assert (res);
          tmp2 = btor_bv_and (g_mm, bvand, res);
          assert (!btor_bv_compare (tmp2, bvand));
          btor_bv_free (g_mm, res);
          btor_bv_free (g_mm, tmp2);
        }

        if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
          goto DONE;

        /* sls engine: only fixable if non-const inputs */
        slv         = g_btor->slv;
        g_btor->slv = btor_new_sls_solver (g_btor);
        btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

        goto PROP_INV_CONF_AND_TESTS;
      DONE:
        btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
        g_btor->slv->api.delet (g_btor->slv);
        g_btor->slv = slv;
      }
      btor_bv_free (g_mm, bvand);
      btor_bv_free (g_mm, tmp);
    }
    btor_node_release (g_btor, cand[0]);
    btor_node_release (g_btor, cand[1]);
    btor_node_release (g_btor, ce[0]);
    btor_node_release (g_btor, ce[1]);
    btor_bv_free (g_mm, bve[0]);
    btor_bv_free (g_mm, bve[1]);
  }

  TEST_PROP_INV_CONF_BINARY_FINISH (and);
#endif
}

static void
prop_inv_conf_ult_bv (uint32_t bw)
{
  (void) bw;
#ifndef NDEBUG
  BtorNode *ult, *e[2], *cult, *ce;
  BtorSortId sort;
  BtorBitVector *res, *bvult, *bve, *zero, *bvmax;
  BtorSolver *slv = 0;

  TEST_PROP_INV_CONF_BINARY_INIT (ult, btor_exp_bv_ult);

  zero  = btor_bv_new (g_mm, bw);
  bvmax = btor_bv_ones (g_mm, bw);
  bvult = btor_bv_one (g_mm, 1);

  /* prop engine: all conflicts are treated as fixable */

PROP_INV_CONF_ULT_TESTS:
  /* 1...1 < e[1] */
  bve = btor_bv_ones (g_mm, bw);
  res = inv_ult_bv (g_btor, ult, bvult, bve, 1);
  assert (res);
  assert (btor_bv_compare (res, zero) > 0);
  btor_bv_free (g_mm, res);
  ce   = btor_exp_bv_const (g_btor, bve);
  cult = btor_exp_bv_ult (g_btor, ce, e[1]);
  res  = inv_ult_bv (g_btor, cult, bvult, bve, 1);
  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
    assert (!res);
  else
  {
    assert (res);
    assert (btor_bv_compare (res, zero) > 0);
    btor_bv_free (g_mm, res);
  }
  btor_node_release (g_btor, cult);
  btor_node_release (g_btor, ce);
  btor_bv_free (g_mm, bve);
  /* e[0] < 0 */
  bve = btor_bv_new (g_mm, bw);
  res = inv_ult_bv (g_btor, ult, bvult, bve, 0);
  assert (res);
  assert (btor_bv_compare (res, bvmax) < 0);
  btor_bv_free (g_mm, res);
  ce   = btor_exp_bv_const (g_btor, bve);
  cult = btor_exp_bv_ult (g_btor, e[0], ce);
  res  = inv_ult_bv (g_btor, cult, bvult, bve, 0);
  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
    assert (!res);
  else
  {
    assert (res);
    assert (btor_bv_compare (res, bvmax) < 0);
    btor_bv_free (g_mm, res);
  }
  btor_node_release (g_btor, cult);
  btor_node_release (g_btor, ce);
  btor_bv_free (g_mm, bve);

  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

  /* sls engine: only fixable if non-const inputs */
  slv         = g_btor->slv;
  g_btor->slv = btor_new_sls_solver (g_btor);
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

  goto PROP_INV_CONF_ULT_TESTS;

DONE:
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
  g_btor->slv->api.delet (g_btor->slv);
  g_btor->slv = slv;

  btor_bv_free (g_mm, bvult);
  btor_bv_free (g_mm, zero);
  btor_bv_free (g_mm, bvmax);

  TEST_PROP_INV_CONF_BINARY_FINISH (ult);
#endif
}

static void
prop_inv_conf_sll_bv (uint32_t bw)
{
  (void) bw;
#ifndef NDEBUG
  int32_t i;
  BtorNode *sll, *e[2], *csll, *ce;
  BtorSortId sort;
  BtorBitVector *res, *bvsll, *bve;
  BtorSolver *slv = 0;

  TEST_PROP_INV_CONF_SHIFT_INIT (sll, btor_exp_bv_sll);

  /* prop engine: all conflicts are treated as fixable */

PROP_INV_CONF_SLL_TESTS:
  /* bve << e[1] = bvsll */

  /* -> shifts by bw are not allowed */
  bvsll = btor_bv_new (g_mm, bw);
  for (i = 0; i < 10; i++)
  {
    bve = btor_bv_new_random (g_mm, &g_btor->rng, bw);
    if (!btor_bv_get_bit (bve, 0)) btor_bv_set_bit (bve, 0, 1);
    ce   = btor_exp_bv_const (g_btor, bve);
    csll = btor_exp_bv_sll (g_btor, ce, e[1]);
    res  = inv_sll_bv (g_btor, sll, bvsll, bve, 1);
    assert (res);
    btor_bv_free (g_mm, res);
    res = inv_sll_bv (g_btor, csll, bvsll, bve, 1);
    assert (
        (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS && !res)
        || (btor_opt_get (g_btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_SLS && res));
    if (res) btor_bv_free (g_mm, res);
    btor_bv_free (g_mm, bve);
    btor_node_release (g_btor, ce);
    btor_node_release (g_btor, csll);
  }
  btor_bv_free (g_mm, bvsll);

  /* -> shifted bits must match */
  switch (bw)
  {
    case 2:
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "00", "01", 0);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "00", "10", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "00", "11", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "01", "11", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "10", "01", 0);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "10", "11", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "11", "01", 0);
      break;

    case 4:
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0000", "0010", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0000", "1000", 3);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0000", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0000", "1110", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0001", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0001", "1100", 2);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0001", "1010", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0001", "1110", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1000", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1000", "1100", 2);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1000", "1010", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1000", "1110", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1010", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1010", "1100", 2);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1010", "1110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1010", "1111", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0110", "0111", 0);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0110", "0010", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0110", "1010", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "0110", "1111", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1111", "1010", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1111", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1111", "0010", 1);
      TEST_PROP_INV_CONF_SHIFT (1, sll, btor_exp_bv_sll, "1111", "0011", 0);
      break;

    case 8:
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "00000000", "11111110", 1);
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "00000000", "10101010", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "00000100", "00111100", 2);
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "00000100", "11110000", 4);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "00100000", "11001100", 2);
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "00100000", "01000010", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "01010101", "10101110", 1);
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "01010101", "10100100", 2);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "11111110", "10111100", 2);
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "11111110", "11111101", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "01111111", "10111100", 2);
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "01111111", "11111101", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "11111111", "10111110", 1);
      TEST_PROP_INV_CONF_SHIFT (
          1, sll, btor_exp_bv_sll, "11111111", "11111101", 0);
      break;

    default: break;
  }

  /* e[0] << bve = bvsll
   * -> LSBs shifted must be zero */
  switch (bw)
  {
    case 2:
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "1", "01", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "1", "11", 0);
      break;
    case 4:
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "01", "0001", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "10", "0110", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "11", "1100", 0);
      break;
    case 8:
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "001", "00000011", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "010", "00001110", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "011", "00001100", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "100", "11111100", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "101", "00011000", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "110", "11001100", 0);
      TEST_PROP_INV_CONF_SHIFT (0, sll, btor_exp_bv_sll, "111", "11000000", 0);
      break;
    default: break;
  }

  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

  /* sls engine: only fixable if non-const inputs */
  slv         = g_btor->slv;
  g_btor->slv = btor_new_sls_solver (g_btor);
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

  goto PROP_INV_CONF_SLL_TESTS;

DONE:
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
  g_btor->slv->api.delet (g_btor->slv);
  g_btor->slv = slv;

  TEST_PROP_INV_CONF_BINARY_FINISH (sll);
#endif
}

static void
prop_inv_conf_srl_bv (uint32_t bw)
{
  (void) bw;
#ifndef NDEBUG
  int32_t i;
  BtorNode *srl, *e[2], *csrl, *ce;
  BtorSortId sort;
  BtorBitVector *res, *bvsrl, *bve;
  BtorSolver *slv = 0;

  TEST_PROP_INV_CONF_SHIFT_INIT (srl, btor_exp_bv_srl);

  /* prop engine: all conflicts are treated as fixable */

PROP_INV_CONF_SRL_TESTS:
  /* bve >> e[1] = bvsrl */

  /* -> shifts by bw are not allowed */
  bvsrl = btor_bv_new (g_mm, bw);
  for (i = 0; i < 10; i++)
  {
    bve = btor_bv_new_random (g_mm, &g_btor->rng, bw);
    if (!btor_bv_get_bit (bve, bw - 1)) btor_bv_set_bit (bve, bw - 1, 1);
    ce   = btor_exp_bv_const (g_btor, bve);
    csrl = btor_exp_bv_srl (g_btor, ce, e[1]);
    res  = inv_srl_bv (g_btor, srl, bvsrl, bve, 1);
    assert (res);
    btor_bv_free (g_mm, res);
    res = inv_srl_bv (g_btor, csrl, bvsrl, bve, 1);
    assert (
        (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS && !res)
        || (btor_opt_get (g_btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_SLS && res));
    if (res) btor_bv_free (g_mm, res);
    btor_bv_free (g_mm, bve);
    btor_node_release (g_btor, ce);
    btor_node_release (g_btor, csrl);
  }
  btor_bv_free (g_mm, bvsrl);

  /* -> shifted bits must match */
  switch (bw)
  {
    case 2:
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "00", "01", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "00", "10", 0);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "00", "11", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "01", "10", 0);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "01", "11", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "10", "11", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "11", "10", 0);
      break;

    case 4:
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0000", "0010", 2);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0000", "1000", 0);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0000", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0000", "1110", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0001", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0001", "0011", 2);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0001", "0101", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0001", "0111", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1000", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1000", "0011", 2);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1000", "0101", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1000", "0111", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1010", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1010", "0011", 2);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1010", "0111", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1010", "1111", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0110", "0111", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0110", "0010", 2);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0110", "1010", 0);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "0110", "1111", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1111", "0101", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1111", "0110", 1);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1111", "0010", 2);
      TEST_PROP_INV_CONF_SHIFT (1, srl, btor_exp_bv_srl, "1111", "0100", 1);
      break;

    case 8:
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "00000000", "01111111", 1);
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "00000000", "01010101", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "00000100", "00111100", 2);
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "00000100", "00001111", 4);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "00100000", "11001100", 0);
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "00100000", "01000010", 1);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "01010101", "01010111", 1);
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "01010101", "00101001", 2);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "11111110", "10111100", 0);
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "11111110", "11111101", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "01111111", "00101111", 2);
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "01111111", "11111101", 0);
      ///
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "11111111", "01011111", 1);
      TEST_PROP_INV_CONF_SHIFT (
          1, srl, btor_exp_bv_srl, "11111111", "11111101", 0);
      break;

    default: break;
  }

  /* e[0] << bve = bvsrl
   * -> LSBs shifted must be zero */
  switch (bw)
  {
    case 2:
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "1", "10", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "1", "11", 0);
      break;
    case 4:
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "01", "1000", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "10", "0110", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "11", "0011", 0);
      break;
    case 8:
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "001", "11000000", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "010", "01110000", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "011", "00110000", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "100", "00111111", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "101", "00011000", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "110", "00110011", 0);
      TEST_PROP_INV_CONF_SHIFT (0, srl, btor_exp_bv_srl, "111", "00000011", 0);
      break;
    default: break;
  }

  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

  /* sls engine: only fixable if non-const inputs */
  slv         = g_btor->slv;
  g_btor->slv = btor_new_sls_solver (g_btor);
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

  goto PROP_INV_CONF_SRL_TESTS;

DONE:
  TEST_PROP_INV_CONF_BINARY_FINISH (srl);

  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
  g_btor->slv->api.delet (g_btor->slv);
  g_btor->slv = slv;
#endif
}

static void
prop_inv_conf_mul_bv (uint32_t bw)
{
  (void) bw;
#ifndef NDEBUG
  uint32_t i, j, k, r;
  BtorNode *mul, *e[2], *cmul[2], *ce[2];
  BtorSortId sort;
  BtorBitVector *res, *bvmul, *bve;
  BtorSolver *slv = 0;

  TEST_PROP_INV_CONF_BINARY_INIT (mul, btor_exp_bv_mul);

  /* prop engine: all conflicts are treated as fixable */

PROP_INV_CONF_MUL_TESTS:
  /* bve = 0 but bvmul > 0 */
  bve     = btor_bv_new (g_mm, bw);
  ce[0]   = btor_exp_bv_const (g_btor, bve);
  ce[1]   = btor_exp_bv_const (g_btor, bve);
  cmul[0] = btor_exp_bv_mul (g_btor, ce[0], e[1]);
  cmul[1] = btor_exp_bv_mul (g_btor, e[0], ce[1]);
  for (k = 0; k < 10; k++)
  {
    bvmul = btor_bv_new_random (g_mm, &g_btor->rng, bw);
    while (btor_bv_is_zero (bvmul))
    {
      btor_bv_free (g_mm, bvmul);
      bvmul = btor_bv_new_random (g_mm, &g_btor->rng, bw);
    }
    TEST_PROP_INV_CONF_MUL (false);
    btor_bv_free (g_mm, bvmul);
  }
  btor_node_release (g_btor, cmul[0]);
  btor_node_release (g_btor, cmul[1]);
  btor_node_release (g_btor, ce[0]);
  btor_node_release (g_btor, ce[1]);
  btor_bv_free (g_mm, bve);

  /* bvmul is odd but bve is even */
  for (k = 0; k < 10; k++)
  {
    bvmul = btor_bv_new_random (g_mm, &g_btor->rng, bw);
    if (!btor_bv_get_bit (bvmul, 0)) btor_bv_set_bit (bvmul, 0, 1);
    bve = btor_bv_new_random (g_mm, &g_btor->rng, bw);
    if (btor_bv_get_bit (bve, 0)) btor_bv_set_bit (bve, 0, 0);
    TEST_PROP_INV_CONF_MUL (true);
    btor_bv_free (g_mm, bvmul);
    btor_bv_free (g_mm, bve);
  }

  /* bve = 2^i and number of 0-LSBs in bvmul < i */
  for (k = 0; k < 10; k++)
  {
    for (i = 1; bw > 1 && i < bw; i++)
    {
      bve = btor_bv_new (g_mm, bw);
      btor_bv_set_bit (bve, i, 1);
      bvmul = btor_bv_new_random (g_mm, &g_btor->rng, bw);
      r     = btor_rng_pick_rand (&g_btor->rng, 0, i - 1);
      for (j = 0; j < r; j++) btor_bv_set_bit (bvmul, j, 0);
      if (!btor_bv_get_bit (bvmul, r)) btor_bv_set_bit (bvmul, r, 1);
      TEST_PROP_INV_CONF_MUL (true);
      btor_bv_free (g_mm, bvmul);
      btor_bv_free (g_mm, bve);
    }
  }

  /* bve = 2^i * m and number of 0-LSBs in bvmul < i */
  for (k = 0; k < 10; k++)
  {
    for (i = 0; bw > 1 && i < 10; i++)
    {
      bve = btor_bv_new_random (g_mm, &g_btor->rng, bw);
      while (btor_bv_power_of_two (bve) >= 0)
      {
        btor_bv_free (g_mm, bve);
        bve = btor_bv_new_random (g_mm, &g_btor->rng, bw);
      }
      if (btor_bv_get_bit (bve, 0))
      {
        r = btor_rng_pick_rand (&g_btor->rng, 1, bw - 1);
        for (j = 0; j < r; j++) btor_bv_set_bit (bve, j, 0);
      }
      else
      {
        for (j = 0; j < bw; j++)
          if (btor_bv_get_bit (bve, j)) break;
      }
      bvmul = btor_bv_new_random (g_mm, &g_btor->rng, bw);
      r     = btor_rng_pick_rand (&g_btor->rng, 0, j - 1);
      for (j = 0; j < r; j++) btor_bv_set_bit (bvmul, j, 0);
      if (!btor_bv_get_bit (bvmul, r)) btor_bv_set_bit (bvmul, r, 1);
      TEST_PROP_INV_CONF_MUL (true);
      btor_bv_free (g_mm, bvmul);
      btor_bv_free (g_mm, bve);
    }
  }

  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

  /* sls engine: only fixable if non-const inputs */
  slv         = g_btor->slv;
  g_btor->slv = btor_new_sls_solver (g_btor);
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);
  goto PROP_INV_CONF_MUL_TESTS;

DONE:
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
  g_btor->slv->api.delet (g_btor->slv);
  g_btor->slv = slv;

  TEST_PROP_INV_CONF_BINARY_FINISH (mul);
#endif
}

static void
prop_inv_conf_udiv_bv (uint32_t bw)
{
  (void) bw;
#ifndef NDEBUG
  int32_t k;
  BtorNode *udiv, *e[2], *cudiv, *ce;
  BtorSortId sort;
  BtorBitVector *res, *bve, *bvudiv, *bvmax, *zero, *tmp, *tmp2;
  BtorSolver *slv = 0;

  TEST_PROP_INV_CONF_BINARY_INIT (udiv, btor_exp_bv_udiv);

  zero  = btor_bv_new (g_mm, bw);
  bvmax = btor_bv_ones (g_mm, bw);

  /* prop engine: all conflicts are treated as fixable */

PROP_INV_CONF_UDIV_TESTS:
  /* bve / e[1] = bvudiv */
  /* bve = 1...1 and bvudiv = 0 */
  bve    = btor_bv_copy (g_mm, bvmax);
  bvudiv = btor_bv_new (g_mm, bw);
  TEST_PROP_INV_CONF_UDIV (1);
  btor_bv_free (g_mm, bvudiv);
  btor_bv_free (g_mm, bve);
  /* bve < bvudiv */
  for (k = 0; bw > 1 && k < 10; k++)
  {
    tmp = btor_bv_uint64_to_bv (g_mm, 2, bw);
    bve = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, zero, tmp);
    btor_bv_free (g_mm, tmp);
    tmp    = btor_bv_inc (g_mm, bve);
    tmp2   = btor_bv_dec (g_mm, bvmax);
    bvudiv = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, tmp, tmp2);
    btor_bv_free (g_mm, tmp);
    btor_bv_free (g_mm, tmp2);
    TEST_PROP_INV_CONF_UDIV (1);
    btor_bv_free (g_mm, bvudiv);
    btor_bv_free (g_mm, bve);
  }
  /* e[0] / bve = bvudiv */
  /* bve = 0 and bvudiv < 1...1 */
  for (k = 0; k < 10; k++)
  {
    bve    = btor_bv_new (g_mm, bw);
    tmp    = btor_bv_dec (g_mm, bvmax);
    bvudiv = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, zero, tmp);
    btor_bv_free (g_mm, tmp);
    TEST_PROP_INV_CONF_UDIV (0);
    btor_bv_free (g_mm, bvudiv);
    btor_bv_free (g_mm, bve);
  }
  /* bvudiv = 1...1 and bve > 1 */
  for (k = 0; bw > 1 && k < 10; k++)
  {
    bvudiv = btor_bv_copy (g_mm, bvmax);
    tmp    = btor_bv_uint64_to_bv (g_mm, 2, bw);
    bve    = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, tmp, bvmax);
    btor_bv_free (g_mm, tmp);
    TEST_PROP_INV_CONF_UDIV (0);
    btor_bv_free (g_mm, bvudiv);
    btor_bv_free (g_mm, bve);
  }

  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

  /* sls engine: only fixable if non-const inputs */
  slv         = g_btor->slv;
  g_btor->slv = btor_new_sls_solver (g_btor);
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

  goto PROP_INV_CONF_UDIV_TESTS;
DONE:
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
  g_btor->slv->api.delet (g_btor->slv);
  g_btor->slv = slv;

  btor_bv_free (g_mm, bvmax);
  btor_bv_free (g_mm, zero);

  TEST_PROP_INV_CONF_BINARY_FINISH (udiv);
#endif
}

static void
prop_inv_conf_urem_bv (uint32_t bw)
{
  (void) bw;
#ifndef NDEBUG
  int32_t k;
  BtorNode *urem, *e[2], *curem, *ce;
  BtorSortId sort;
  BtorBitVector *res, *bve, *bvurem, *bvmax, *zero, *two, *tmp, *tmp2;
  BtorSolver *slv = 0;

  TEST_PROP_INV_CONF_BINARY_INIT (urem, btor_exp_bv_urem);

  zero  = btor_bv_new (g_mm, bw);
  bvmax = btor_bv_ones (g_mm, bw);

  /* prop engine: all conflicts are treated as fixable */

PROP_INV_CONF_UREM_TESTS:
  /* bve % e[1] = bvurem */
  /* bvurem = 1...1 and bve < 1...1 */
  bvurem = btor_bv_copy (g_mm, bvmax);
  for (k = 0; k < 10; k++)
  {
    tmp   = btor_bv_dec (g_mm, bvmax);
    bve   = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, zero, tmp);
    ce    = btor_exp_bv_const (g_btor, bve);
    curem = btor_exp_bv_urem (g_btor, ce, e[1]);
    res   = inv_urem_bv (g_btor, urem, bvurem, bve, 1);
    assert (res);
    assert (btor_bv_is_zero (res));
    btor_bv_free (g_mm, res);
    res = inv_urem_bv (g_btor, curem, bvurem, bve, 1);
    if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      assert (!res);
    else
    {
      assert (res);
      assert (btor_bv_is_zero (res));
      btor_bv_free (g_mm, res);
    }
    btor_node_release (g_btor, curem);
    btor_node_release (g_btor, ce);
    btor_bv_free (g_mm, tmp);
    btor_bv_free (g_mm, bve);
  }
  btor_bv_free (g_mm, bvurem);
  /* bve < bvurem */
  for (k = 0; k < 10; k++)
  {
    tmp    = btor_bv_inc (g_mm, zero);
    bvurem = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, tmp, bvmax);
    btor_bv_free (g_mm, tmp);
    tmp = btor_bv_dec (g_mm, bvurem);
    bve = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, zero, tmp);
    btor_bv_free (g_mm, tmp);
    ce    = btor_exp_bv_const (g_btor, bve);
    curem = btor_exp_bv_urem (g_btor, ce, e[1]);
    res   = inv_urem_bv (g_btor, urem, bvurem, bve, 1);
    assert (res);
    btor_bv_free (g_mm, res);
    res = inv_urem_bv (g_btor, curem, bvurem, bve, 1);
    if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      assert (!res);
    else
    {
      assert (res);
      btor_bv_free (g_mm, res);
    }
    btor_node_release (g_btor, curem);
    btor_node_release (g_btor, ce);
    btor_bv_free (g_mm, bve);
    btor_bv_free (g_mm, bvurem);
  }
  /* bve > bvurem and bve - bvurem <= bvurem -> bve > 2 * bvurem */
  for (k = 0; bw > 1 && k < 10; k++)
  {
    two    = btor_bv_uint64_to_bv (g_mm, 2, bw);
    tmp2   = btor_bv_udiv (g_mm, bvmax, two);
    tmp    = btor_bv_uint64_to_bv (g_mm, 1, bw);
    bvurem = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, tmp, tmp2);
    btor_bv_free (g_mm, tmp);
    btor_bv_free (g_mm, tmp2);
    tmp  = btor_bv_inc (g_mm, bvurem);
    tmp2 = btor_bv_mul (g_mm, bvurem, two);
    bve  = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, tmp, tmp2);
    btor_bv_free (g_mm, tmp);
    btor_bv_free (g_mm, tmp2);
    ce    = btor_exp_bv_const (g_btor, bve);
    curem = btor_exp_bv_urem (g_btor, ce, e[1]);
    res   = inv_urem_bv (g_btor, urem, bvurem, bve, 1);
    assert (res);
    btor_bv_free (g_mm, res);
    res = inv_urem_bv (g_btor, curem, bvurem, bve, 1);
    if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      assert (!res);
    else
    {
      assert (res);
      btor_bv_free (g_mm, res);
    }
    btor_node_release (g_btor, curem);
    btor_node_release (g_btor, ce);
    btor_bv_free (g_mm, two);
    btor_bv_free (g_mm, bvurem);
    btor_bv_free (g_mm, bve);
  }

  /* e[0] % bve = bvurem */
  /* bvurem = 1...1 and bve > 0 */
  bvurem = btor_bv_copy (g_mm, bvmax);
  for (k = 0; k < 10; k++)
  {
    tmp   = btor_bv_inc (g_mm, zero);
    bve   = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, tmp, bvmax);
    ce    = btor_exp_bv_const (g_btor, bve);
    curem = btor_exp_bv_urem (g_btor, e[0], ce);
    res   = inv_urem_bv (g_btor, urem, bvurem, bve, 0);
    assert (res);
    assert (!btor_bv_compare (res, bvurem));
    btor_bv_free (g_mm, res);
    res = inv_urem_bv (g_btor, curem, bvurem, bve, 0);
    if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      assert (!res);
    else
    {
      assert (res);
      assert (!btor_bv_compare (res, bvurem));
      btor_bv_free (g_mm, res);
    }
    btor_node_release (g_btor, curem);
    btor_node_release (g_btor, ce);
    btor_bv_free (g_mm, tmp);
    btor_bv_free (g_mm, bve);
  }
  btor_bv_free (g_mm, bvurem);
  /* bve > 0 and bve <= bvurem */
  for (k = 0; bw > 1 && k < 10; k++)
  {
    tmp    = btor_bv_inc (g_mm, zero);
    bvurem = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, tmp, bvmax);
    bve    = btor_bv_new_random_range (g_mm, &g_btor->rng, bw, tmp, bvurem);
    ce     = btor_exp_bv_const (g_btor, bve);
    curem  = btor_exp_bv_urem (g_btor, e[0], ce);
    res    = inv_urem_bv (g_btor, urem, bvurem, bve, 0);
    assert (res);
    btor_bv_free (g_mm, res);
    res = inv_urem_bv (g_btor, curem, bvurem, bve, 0);
    if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      assert (!res);
    else
    {
      assert (res);
      btor_bv_free (g_mm, res);
    }
    btor_node_release (g_btor, curem);
    btor_node_release (g_btor, ce);
    btor_bv_free (g_mm, tmp);
    btor_bv_free (g_mm, bvurem);
    btor_bv_free (g_mm, bve);
  }

  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

  /* sls engine: only fixable if non-const inputs */
  slv         = g_btor->slv;
  g_btor->slv = btor_new_sls_solver (g_btor);
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

  goto PROP_INV_CONF_UREM_TESTS;

DONE:
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
  g_btor->slv->api.delet (g_btor->slv);
  g_btor->slv = slv;

  btor_bv_free (g_mm, zero);
  btor_bv_free (g_mm, bvmax);
  TEST_PROP_INV_CONF_BINARY_FINISH (urem);
#endif
}

static void
prop_inv_conf_concat_bv (uint32_t bw)
{
  (void) bw;
#ifndef NDEBUG
  int32_t k, cnt;
  uint32_t i, j, bws[2];
  BtorNode *concat, *e[2], *ce[2], *cconcat[2];
  BtorSortId sorts[2];
  BtorBitVector *res, *bvconcat, *bve[2], *tmp[2];
  BtorSolver *slv = 0;

  /* prop engine: all conflicts are treated as fixable */

PROP_INV_CONF_CONCAT_TESTS:

  for (k = 0; bw > 1 && k < 10; k++)
  {
    bws[0]   = btor_rng_pick_rand (&g_btor->rng, 1, bw - 1);
    bws[1]   = bw - bws[0];
    sorts[0] = btor_sort_bv (g_btor, bw);
    sorts[1] = btor_sort_bv (g_btor, bw);
    e[0]     = btor_exp_var (g_btor, sorts[0], 0);
    e[1]     = btor_exp_var (g_btor, sorts[1], 0);
    concat   = btor_exp_bv_concat (g_btor, e[0], e[1]);
    bvconcat = btor_bv_new_random (g_mm, &g_btor->rng, bw);
    for (j = 0; j < 2; j++)
    {
      bve[j] = btor_bv_slice (
          g_mm, bvconcat, j ? bws[1] - 1 : bw - 1, j ? 0 : bws[1]);
      assert (bve[j]->width == bws[j]);
      tmp[j] = btor_bv_copy (g_mm, bve[j]);
      cnt    = 0;
      while (!cnt)
      {
        for (i = 0; i < bws[j]; i++)
        {
          if (btor_rng_pick_rand (&g_btor->rng, 0, 5))
          {
            btor_bv_set_bit (bve[j], i, btor_bv_get_bit (bve[j], i) ? 0 : 1);
            cnt += 1;
          }
        }
      }
    }
    ce[0]      = btor_exp_bv_const (g_btor, bve[0]);
    ce[1]      = btor_exp_bv_const (g_btor, bve[1]);
    cconcat[0] = btor_exp_bv_concat (g_btor, ce[0], e[1]);
    cconcat[1] = btor_exp_bv_concat (g_btor, e[0], ce[1]);
    for (j = 0; j < 2; j++)
    {
      res = inv_concat_bv (g_btor, concat, bvconcat, bve[j ? 0 : 1], j);
      assert (res);
      assert (!btor_bv_compare (res, tmp[j]));
      btor_bv_free (g_mm, res);
      res = inv_concat_bv (
          g_btor, cconcat[j ? 0 : 1], bvconcat, bve[j ? 0 : 1], j);
      if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
        assert (!res);
      else
      {
        assert (res);
        assert (!btor_bv_compare (res, tmp[j]));
        btor_bv_free (g_mm, res);
      }
    }
    for (j = 0; j < 2; j++)
    {
      btor_sort_release (g_btor, sorts[j]);
      btor_node_release (g_btor, cconcat[j]);
      btor_node_release (g_btor, ce[j]);
      btor_node_release (g_btor, e[j]);
      btor_bv_free (g_mm, bve[j]);
      btor_bv_free (g_mm, tmp[j]);
    }

    btor_node_release (g_btor, concat);
    btor_bv_free (g_mm, bvconcat);
  }

  if (btor_opt_get (g_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

  /* sls engine: only fixable if non-const inputs */
  slv         = g_btor->slv;
  g_btor->slv = btor_new_sls_solver (g_btor);
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

  goto PROP_INV_CONF_CONCAT_TESTS;

DONE:
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
  g_btor->slv->api.delet (g_btor->slv);
  g_btor->slv = slv;
#endif
}

static void
test_propinv_conf_and_bv (void)
{
  prop_inv_conf_and_bv (1);
  prop_inv_conf_and_bv (4);
  prop_inv_conf_and_bv (8);
}

static void
test_propinv_conf_ult_bv (void)
{
  prop_inv_conf_ult_bv (1);
  prop_inv_conf_ult_bv (4);
  prop_inv_conf_ult_bv (8);
}

static void
test_propinv_conf_sll_bv (void)
{
  prop_inv_conf_sll_bv (2);
  prop_inv_conf_sll_bv (4);
  prop_inv_conf_sll_bv (8);
}

static void
test_propinv_conf_srl_bv (void)
{
  prop_inv_conf_srl_bv (2);
  prop_inv_conf_srl_bv (4);
  prop_inv_conf_srl_bv (8);
}

static void
test_propinv_conf_mul_bv (void)
{
  prop_inv_conf_mul_bv (1);
  prop_inv_conf_mul_bv (4);
  prop_inv_conf_mul_bv (8);
}

static void
test_propinv_conf_udiv_bv (void)
{
  prop_inv_conf_udiv_bv (1);
  prop_inv_conf_udiv_bv (4);
  prop_inv_conf_udiv_bv (8);
}

static void
test_propinv_conf_urem_bv (void)
{
  prop_inv_conf_urem_bv (1);
  prop_inv_conf_urem_bv (4);
  prop_inv_conf_urem_bv (8);
}

static void
test_propinv_conf_concat_bv (void)
{
  prop_inv_conf_concat_bv (2);
  prop_inv_conf_concat_bv (4);
  prop_inv_conf_concat_bv (8);
}

/*------------------------------------------------------------------------*/

void
init_propinv_tests (void)
{
  g_btor            = btor_new ();
  g_btor->slv       = btor_new_prop_solver (g_btor);
  g_btor->slv->btor = g_btor;
  btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
  btor_opt_set (g_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  btor_opt_set (g_btor, BTOR_OPT_SORT_EXP, 0);
  btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_CONC_FLIP, 0);
  btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_SLICE_FLIP, 0);
  btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_EQ_FLIP, 0);
  btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_AND_FLIP, 0);
  g_mm  = g_btor->mm;
  g_rng = &g_btor->rng;
  btor_model_init_bv (g_btor, &g_btor->bv_model);
  btor_model_init_fun (g_btor, &g_btor->fun_model);
  btor_model_generate (g_btor, g_btor->bv_model, g_btor->fun_model, 0);
}

void
run_propinv_tests (int32_t argc, char **argv)
{
  (void) argc;
  (void) argv;
  BTOR_RUN_TEST (propinv_conf_and_bv);
  BTOR_RUN_TEST (propinv_conf_ult_bv);
  BTOR_RUN_TEST (propinv_conf_sll_bv);
  BTOR_RUN_TEST (propinv_conf_srl_bv);
  BTOR_RUN_TEST (propinv_conf_mul_bv);
  BTOR_RUN_TEST (propinv_conf_udiv_bv);
  BTOR_RUN_TEST (propinv_conf_urem_bv);
  BTOR_RUN_TEST (propinv_conf_concat_bv);

  BTOR_RUN_TEST (propinv_complete_add_bv);
  BTOR_RUN_TEST (propinv_complete_and_bv);
  BTOR_RUN_TEST (propinv_complete_eq_bv);
  BTOR_RUN_TEST (propinv_complete_ult_bv);
  BTOR_RUN_TEST (propinv_complete_sll_bv);
  BTOR_RUN_TEST (propinv_complete_srl_bv);
  BTOR_RUN_TEST (propinv_complete_mul_bv);
  BTOR_RUN_TEST (propinv_complete_udiv_bv);
  BTOR_RUN_TEST (propinv_complete_urem_bv);
  BTOR_RUN_TEST (propinv_complete_concat_bv);
  BTOR_RUN_TEST (propinv_complete_slice_bv);
}

void
finish_propinv_tests (void)
{
  btor_delete (g_btor);
}

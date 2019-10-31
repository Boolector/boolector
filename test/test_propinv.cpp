/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "btorbv.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btornode.h"
#include "btorproputils.h"
#include "utils/btorutil.h"
}

class TestPropInv : public TestBtor
{
 protected:
  static constexpr uint32_t TEST_PROP_INV_COMPLETE_BW      = 4u;
  static constexpr uint64_t TEST_PROP_INV_COMPLETE_N_TESTS = 10000u;

  void SetUp () override
  {
    TestBtor::SetUp ();

    d_btor->slv       = btor_new_prop_solver (d_btor);
    d_btor->slv->btor = d_btor;
    d_mm              = d_btor->mm;
    d_rng             = &d_btor->rng;

    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    btor_opt_set (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
    btor_opt_set (d_btor, BTOR_OPT_SORT_EXP, 0);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_CONC_FLIP, 0);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_SLICE_FLIP, 0);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_EQ_FLIP, 0);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_AND_FLIP, 0);

    btor_model_init_bv (d_btor, &d_btor->bv_model);
    btor_model_init_fun (d_btor, &d_btor->fun_model);
    btor_model_generate (d_btor, d_btor->bv_model, d_btor->fun_model, 0);
  }

  void check_result (BtorBitVector *(*inv_fun) (Btor *,
                                                BtorNode *,
                                                BtorBitVector *,
                                                BtorBitVector *,
                                                int32_t eidx),
                     BtorNode *exp,
                     BtorBitVector *bve,
                     BtorBitVector *bvn,
                     BtorBitVector *bvres,
                     uint32_t eidx)
  {
    uint64_t k;
    BtorBitVector *res;

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      res = inv_fun (d_btor, exp, bvn, bve, eidx);
      ASSERT_NE (res, nullptr);
      if (!btor_bv_compare (res, bvres)) break;
      btor_bv_free (d_mm, res);
      res = 0;
    }
    ASSERT_NE (res, nullptr);
    ASSERT_EQ (btor_bv_compare (res, bvres), 0);
    btor_bv_free (d_mm, res);
  }

  void check_binary (BtorNode *(*exp_fun) (Btor *, BtorNode *, BtorNode *),
                     BtorBitVector *(*bv_fun) (BtorMemMgr *,
                                               const BtorBitVector *,
                                               const BtorBitVector *),
                     BtorBitVector *(*inv_fun) (Btor *,
                                                BtorNode *,
                                                BtorBitVector *,
                                                BtorBitVector *,
                                                int32_t eidx))
  {
    uint32_t bw;
    uint64_t i, j;
    BtorNode *exp, *e[2];
    BtorSortId sort;
    BtorBitVector *bve[2], *bvexp;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    exp = exp_fun (d_btor, e[0], e[1]);

    for (i = 0; i < (uint32_t) (1 << bw); i++)
    {
      bve[0] = btor_bv_uint64_to_bv (d_mm, i, bw);
      for (j = 0; j < (uint32_t) (1 << bw); j++)
      {
        bve[1] = btor_bv_uint64_to_bv (d_mm, j, bw);
        bvexp  = bv_fun (d_mm, bve[0], bve[1]);
        check_result (inv_fun, exp, bve[0], bvexp, bve[1], 1);
        check_result (inv_fun, exp, bve[1], bvexp, bve[0], 0);
        btor_bv_free (d_mm, bve[1]);
        btor_bv_free (d_mm, bvexp);
      }
      btor_bv_free (d_mm, bve[0]);
    }
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
    btor_node_release (d_btor, exp);
  }

  void check_shift (BtorNode *(*exp_fun) (Btor *, BtorNode *, BtorNode *),
                    BtorBitVector *(*bv_fun) (BtorMemMgr *,
                                              const BtorBitVector *,
                                              const BtorBitVector *),
                    BtorBitVector *(*inv_fun) (Btor *,
                                               BtorNode *,
                                               BtorBitVector *,
                                               BtorBitVector *,
                                               int32_t eidx))
  {
    uint32_t bw;
    uint64_t i, j;
    BtorNode *exp, *e[2];
    BtorSortId sort;
    BtorBitVector *bve[2], *bvexp;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    exp = exp_fun (d_btor, e[0], e[1]);

    for (i = 0; i < (uint32_t) (1 << bw); i++)
    {
      bve[0] = btor_bv_uint64_to_bv (d_mm, i, bw);
      for (j = 0; j < (uint32_t) (1 << bw); j++)
      {
        bve[1] = btor_bv_uint64_to_bv (d_mm, j, bw);
        bvexp  = bv_fun (d_mm, bve[0], bve[1]);
        check_result (inv_fun, exp, bve[0], bvexp, bve[1], 1);
        check_result (inv_fun, exp, bve[1], bvexp, bve[0], 0);
        btor_bv_free (d_mm, bve[1]);
        btor_bv_free (d_mm, bvexp);
      }
      btor_bv_free (d_mm, bve[0]);
    }
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
    btor_node_release (d_btor, exp);
  }

  void check_conf_and (uint32_t bw)
  {
#ifndef NDEBUG
    (void) bw;
    uint64_t i, j;
    BtorNode *_and, *cand[2], *e[2], *ce[2];
    BtorSortId sort;
    BtorBitVector *bvand, *bve[2], *res, *tmp, *tmp2;
    BtorSolver *slv = 0;

    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    _and = btor_exp_bv_and (d_btor, e[0], e[1]);

    for (i = 0; i < (uint32_t) (1 << bw); i++)
    {
      bve[0]  = btor_bv_uint64_to_bv (d_mm, i, bw);
      bve[1]  = btor_bv_uint64_to_bv (d_mm, i, bw);
      ce[0]   = btor_exp_bv_const (d_btor, bve[0]);
      ce[1]   = btor_exp_bv_const (d_btor, bve[1]);
      cand[0] = btor_exp_bv_and (d_btor, ce[0], e[1]);
      cand[1] = btor_exp_bv_and (d_btor, e[0], ce[1]);

      for (j = 0; j < (uint32_t) (1 << bw); j++)
      {
        bvand = btor_bv_uint64_to_bv (d_mm, j, bw);
        tmp   = btor_bv_and (d_mm, bve[0], bvand);
        if (btor_bv_compare (tmp, bvand))
        {
        PROP_INV_CONF_AND_TESTS:
          /* prop engine: all conflicts are treated as fixable */
          res = inv_and_bv (d_btor, _and, bvand, bve[1], 0);
          ASSERT_NE (res, nullptr);
          tmp2 = btor_bv_and (d_mm, bvand, res);
          ASSERT_EQ (btor_bv_compare (tmp2, bvand), 0);
          btor_bv_free (d_mm, res);
          btor_bv_free (d_mm, tmp2);

          res = inv_and_bv (d_btor, _and, bvand, bve[0], 1);
          ASSERT_NE (res, nullptr);
          tmp2 = btor_bv_and (d_mm, bvand, res);
          ASSERT_EQ (btor_bv_compare (tmp2, bvand), 0);
          btor_bv_free (d_mm, res);
          btor_bv_free (d_mm, tmp2);

          res = inv_and_bv (d_btor, cand[0], bvand, bve[0], 1);
          if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
          {
            ASSERT_EQ (res, nullptr);
          }
          else
          {
            ASSERT_NE (res, nullptr);
            tmp2 = btor_bv_and (d_mm, bvand, res);
            ASSERT_EQ (btor_bv_compare (tmp2, bvand), 0);
            btor_bv_free (d_mm, res);
            btor_bv_free (d_mm, tmp2);
          }

          res = inv_and_bv (d_btor, cand[1], bvand, bve[1], 0);
          if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
          {
            ASSERT_EQ (res, nullptr);
          }
          else
          {
            ASSERT_NE (res, nullptr);
            tmp2 = btor_bv_and (d_mm, bvand, res);
            ASSERT_EQ (btor_bv_compare (tmp2, bvand), 0);
            btor_bv_free (d_mm, res);
            btor_bv_free (d_mm, tmp2);
          }

          if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
            goto DONE;

          /* sls engine: only fixable if non-const inputs */
          slv         = d_btor->slv;
          d_btor->slv = btor_new_sls_solver (d_btor);
          btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

          goto PROP_INV_CONF_AND_TESTS;
        DONE:
          btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
          d_btor->slv->api.delet (d_btor->slv);
          d_btor->slv = slv;
        }
        btor_bv_free (d_mm, bvand);
        btor_bv_free (d_mm, tmp);
      }
      btor_node_release (d_btor, cand[0]);
      btor_node_release (d_btor, cand[1]);
      btor_node_release (d_btor, ce[0]);
      btor_node_release (d_btor, ce[1]);
      btor_bv_free (d_mm, bve[0]);
      btor_bv_free (d_mm, bve[1]);
    }

    btor_node_release (d_btor, _and);
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_ult (uint32_t bw)
  {
#ifndef NDEBUG
    (void) bw;
    BtorNode *ult, *e[2], *cult, *ce;
    BtorSortId sort;
    BtorBitVector *res, *bvult, *bve, *zero, *bvmax;
    BtorSolver *slv = 0;

    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    ult = btor_exp_bv_ult (d_btor, e[0], e[1]);

    zero  = btor_bv_new (d_mm, bw);
    bvmax = btor_bv_ones (d_mm, bw);
    bvult = btor_bv_one (d_mm, 1);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_ULT_TESTS:
    /* 1...1 < e[1] */
    bve = btor_bv_ones (d_mm, bw);
    res = inv_ult_bv (d_btor, ult, bvult, bve, 1);
    ASSERT_NE (res, nullptr);
    ASSERT_GT (btor_bv_compare (res, zero), 0);
    btor_bv_free (d_mm, res);
    ce   = btor_exp_bv_const (d_btor, bve);
    cult = btor_exp_bv_ult (d_btor, ce, e[1]);
    res  = inv_ult_bv (d_btor, cult, bvult, bve, 1);
    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
    {
      ASSERT_EQ (res, nullptr);
    }
    else
    {
      ASSERT_NE (res, nullptr);
      ASSERT_GT (btor_bv_compare (res, zero), 0);
      btor_bv_free (d_mm, res);
    }
    btor_node_release (d_btor, cult);
    btor_node_release (d_btor, ce);
    btor_bv_free (d_mm, bve);
    /* e[0] < 0 */
    bve = btor_bv_new (d_mm, bw);
    res = inv_ult_bv (d_btor, ult, bvult, bve, 0);
    ASSERT_NE (res, nullptr);
    ASSERT_LT (btor_bv_compare (res, bvmax), 0);
    btor_bv_free (d_mm, res);
    ce   = btor_exp_bv_const (d_btor, bve);
    cult = btor_exp_bv_ult (d_btor, e[0], ce);
    res  = inv_ult_bv (d_btor, cult, bvult, bve, 0);
    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
    {
      ASSERT_EQ (res, nullptr);
    }
    else
    {
      ASSERT_NE (res, nullptr);
      ASSERT_LT (btor_bv_compare (res, bvmax), 0);
      btor_bv_free (d_mm, res);
    }
    btor_node_release (d_btor, cult);
    btor_node_release (d_btor, ce);
    btor_bv_free (d_mm, bve);

    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_btor->slv;
    d_btor->slv = btor_new_sls_solver (d_btor);
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

    goto PROP_INV_CONF_ULT_TESTS;

  DONE:
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    d_btor->slv->api.delet (d_btor->slv);
    d_btor->slv = slv;

    btor_bv_free (d_mm, bvult);
    btor_bv_free (d_mm, zero);
    btor_bv_free (d_mm, bvmax);

    btor_node_release (d_btor, ult);
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_sll (uint32_t bw)
  {
#ifndef NDEBUG
    (void) bw;
    BtorNode *sll, *e[2];
    BtorSortId sort;
    BtorSolver *slv = 0;

    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    sll = btor_exp_bv_sll (d_btor, e[0], e[1]);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_SLL_TESTS:
    /* bve << e[1] = bvsll */

    /* -> shifted bits must match */
    switch (bw)
    {
      case 2:
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00", "01", 0);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00", "10", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00", "11", 0);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "01", "11", 0);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "10", "01", 0);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "10", "11", 0);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "11", "01", 0);
        break;

      case 4:
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0000", "0010", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0000", "1000", 3);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0000", "0110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0000", "1110", 1);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0001", "0110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0001", "1100", 2);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0001", "1010", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0001", "1110", 1);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1000", "0110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1000", "1100", 2);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1000", "1010", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1000", "1110", 1);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1010", "0110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1010", "1100", 2);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1010", "1110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1010", "1111", 0);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0110", "0111", 0);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0110", "0010", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0110", "1010", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "0110", "1111", 0);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1111", "1010", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1111", "0110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1111", "0010", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "1111", "0011", 0);
        break;

      case 8:
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000000", "11111110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000000", "10101010", 1);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000100", "00111100", 2);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000100", "11110000", 4);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00100000", "11001100", 2);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "00100000", "01000010", 1);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "01010101", "10101110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "01010101", "10100100", 2);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "11111110", "10111100", 2);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "11111110", "11111101", 0);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "01111111", "10111100", 2);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "01111111", "11111101", 0);
        ///
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "11111111", "10111110", 1);
        check_conf_shift (
            1, sll, e, btor_exp_bv_sll, inv_sll_bv, "11111111", "11111101", 0);
        break;

      default: break;
    }

    /* e[0] << bve = bvsll
     * -> LSBs shifted must be zero */
    switch (bw)
    {
      case 2:
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "01", "01", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "01", "11", 0);
        break;
      case 4:
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "0001", "0001", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "0010", "0110", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "0011", "1100", 0);
        break;
      case 8:
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000001", "00000011", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000010", "00001110", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000011", "00001100", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000100", "11111100", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000101", "00011000", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000110", "11001100", 0);
        check_conf_shift (
            0, sll, e, btor_exp_bv_sll, inv_sll_bv, "00000111", "11000000", 0);
        break;
      default: break;
    }

    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_btor->slv;
    d_btor->slv = btor_new_sls_solver (d_btor);
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

    goto PROP_INV_CONF_SLL_TESTS;

  DONE:
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    d_btor->slv->api.delet (d_btor->slv);
    d_btor->slv = slv;

    btor_node_release (d_btor, sll);
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_srl (uint32_t bw)
  {
#ifndef NDEBUG
    (void) bw;
    BtorNode *srl, *e[2];
    BtorSortId sort;
    BtorSolver *slv = 0;

    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    srl = btor_exp_bv_srl (d_btor, e[0], e[1]);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_SRL_TESTS:
    /* bve >> e[1] = bvsrl */

    /* -> shifted bits must match */
    switch (bw)
    {
      case 2:
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00", "01", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00", "10", 0);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00", "11", 0);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "01", "10", 0);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "01", "11", 0);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "10", "11", 0);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "11", "10", 0);
        break;

      case 4:
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0000", "0010", 2);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0000", "1000", 0);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0000", "0110", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0000", "1110", 0);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0001", "0110", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0001", "0011", 2);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0001", "0101", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0001", "0111", 1);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1000", "0110", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1000", "0011", 2);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1000", "0101", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1000", "0111", 1);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1010", "0110", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1010", "0011", 2);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1010", "0111", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1010", "1111", 0);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0110", "0111", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0110", "0010", 2);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0110", "1010", 0);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "0110", "1111", 0);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1111", "0101", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1111", "0110", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1111", "0010", 2);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "1111", "0100", 1);
        break;

      case 8:
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000000", "01111111", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000000", "01010101", 1);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000100", "00111100", 2);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000100", "00001111", 4);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00100000", "11001100", 0);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "00100000", "01000010", 1);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "01010101", "01010111", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "01010101", "00101001", 2);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "11111110", "10111100", 0);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "11111110", "11111101", 0);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "01111111", "00101111", 2);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "01111111", "11111101", 0);
        ///
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "11111111", "01011111", 1);
        check_conf_shift (
            1, srl, e, btor_exp_bv_srl, inv_srl_bv, "11111111", "11111101", 0);
        break;

      default: break;
    }

    /* e[0] << bve = bvsrl
     * -> LSBs shifted must be zero */
    switch (bw)
    {
      case 2:
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "01", "10", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "01", "11", 0);
        break;
      case 4:
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "0001", "1000", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "0010", "0110", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "0011", "0011", 0);
        break;
      case 8:
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000001", "11000000", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000010", "01110000", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000011", "00110000", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000100", "00111111", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000101", "00011000", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000110", "00110011", 0);
        check_conf_shift (
            0, srl, e, btor_exp_bv_srl, inv_srl_bv, "00000111", "00000011", 0);
        break;
      default: break;
    }

    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_btor->slv;
    d_btor->slv = btor_new_sls_solver (d_btor);
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

    goto PROP_INV_CONF_SRL_TESTS;

  DONE:
    btor_node_release (d_btor, srl);
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);

    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    d_btor->slv->api.delet (d_btor->slv);
    d_btor->slv = slv;
#else
    (void) bw;
#endif
  }

  void check_conf_mul (uint32_t bw)
  {
#ifndef NDEBUG
    (void) bw;
    uint32_t i, j, k, r;
    BtorNode *mul, *e[2];
    BtorSortId sort;
    BtorBitVector *bvmul, *bve;
    BtorSolver *slv = 0;

    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    mul = btor_exp_bv_mul (d_btor, e[0], e[1]);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_MUL_TESTS:
    /* bve = 0 but bvmul > 0 */
    bve = btor_bv_new (d_mm, bw);
    for (k = 0; k < 10; k++)
    {
      bvmul = btor_bv_new_random (d_mm, &d_btor->rng, bw);
      while (btor_bv_is_zero (bvmul))
      {
        btor_bv_free (d_mm, bvmul);
        bvmul = btor_bv_new_random (d_mm, &d_btor->rng, bw);
      }
      check_conf_mul_result (mul, e, bvmul, bve);
      btor_bv_free (d_mm, bvmul);
    }
    btor_bv_free (d_mm, bve);

    /* bvmul is odd but bve is even */
    for (k = 0; k < 10; k++)
    {
      bvmul = btor_bv_new_random (d_mm, &d_btor->rng, bw);
      if (!btor_bv_get_bit (bvmul, 0)) btor_bv_set_bit (bvmul, 0, 1);
      bve = btor_bv_new_random (d_mm, &d_btor->rng, bw);
      if (btor_bv_get_bit (bve, 0)) btor_bv_set_bit (bve, 0, 0);
      check_conf_mul_result (mul, e, bvmul, bve);
      btor_bv_free (d_mm, bvmul);
      btor_bv_free (d_mm, bve);
    }

    /* bve = 2^i and number of 0-LSBs in bvmul < i */
    for (k = 0; k < 10; k++)
    {
      for (i = 1; bw > 1 && i < bw; i++)
      {
        bve = btor_bv_new (d_mm, bw);
        btor_bv_set_bit (bve, i, 1);
        bvmul = btor_bv_new_random (d_mm, &d_btor->rng, bw);
        r     = btor_rng_pick_rand (&d_btor->rng, 0, i - 1);
        for (j = 0; j < r; j++) btor_bv_set_bit (bvmul, j, 0);
        if (!btor_bv_get_bit (bvmul, r)) btor_bv_set_bit (bvmul, r, 1);
        check_conf_mul_result (mul, e, bvmul, bve);
        btor_bv_free (d_mm, bvmul);
        btor_bv_free (d_mm, bve);
      }
    }

    /* bve = 2^i * m and number of 0-LSBs in bvmul < i */
    for (k = 0; k < 10; k++)
    {
      for (i = 0; bw > 1 && i < 10; i++)
      {
        bve = btor_bv_new_random (d_mm, &d_btor->rng, bw);
        while (btor_bv_power_of_two (bve) >= 0)
        {
          btor_bv_free (d_mm, bve);
          bve = btor_bv_new_random (d_mm, &d_btor->rng, bw);
        }
        if (btor_bv_get_bit (bve, 0))
        {
          r = btor_rng_pick_rand (&d_btor->rng, 1, bw - 1);
          for (j = 0; j < r; j++) btor_bv_set_bit (bve, j, 0);
        }
        else
        {
          for (j = 0; j < bw; j++)
            if (btor_bv_get_bit (bve, j)) break;
        }
        bvmul = btor_bv_new_random (d_mm, &d_btor->rng, bw);
        r     = btor_rng_pick_rand (&d_btor->rng, 0, j - 1);
        for (j = 0; j < r; j++) btor_bv_set_bit (bvmul, j, 0);
        if (!btor_bv_get_bit (bvmul, r)) btor_bv_set_bit (bvmul, r, 1);
        check_conf_mul_result (mul, e, bvmul, bve);
        btor_bv_free (d_mm, bvmul);
        btor_bv_free (d_mm, bve);
      }
    }

    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_btor->slv;
    d_btor->slv = btor_new_sls_solver (d_btor);
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);
    goto PROP_INV_CONF_MUL_TESTS;

  DONE:
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    d_btor->slv->api.delet (d_btor->slv);
    d_btor->slv = slv;

    btor_node_release (d_btor, mul);
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_udiv (uint32_t bw)
  {
#ifndef NDEBUG
    (void) bw;
    int32_t k;
    BtorNode *udiv, *e[2];
    BtorSortId sort;
    BtorBitVector *bve, *bvudiv, *bvmax, *zero, *tmp, *tmp2;
    BtorSolver *slv = 0;

    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    udiv = btor_exp_bv_udiv (d_btor, e[0], e[1]);

    zero  = btor_bv_new (d_mm, bw);
    bvmax = btor_bv_ones (d_mm, bw);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_UDIV_TESTS:
    /* bve / e[1] = bvudiv */
    /* bve = 1...1 and bvudiv = 0 */
    bve    = btor_bv_copy (d_mm, bvmax);
    bvudiv = btor_bv_new (d_mm, bw);
    check_conf_udiv_result (1, udiv, e, bvudiv, bve);
    btor_bv_free (d_mm, bvudiv);
    btor_bv_free (d_mm, bve);
    /* bve < bvudiv */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      tmp = btor_bv_uint64_to_bv (d_mm, 2, bw);
      bve = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, zero, tmp);
      btor_bv_free (d_mm, tmp);
      tmp    = btor_bv_inc (d_mm, bve);
      tmp2   = btor_bv_dec (d_mm, bvmax);
      bvudiv = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, tmp, tmp2);
      btor_bv_free (d_mm, tmp);
      btor_bv_free (d_mm, tmp2);
      check_conf_udiv_result (1, udiv, e, bvudiv, bve);
      btor_bv_free (d_mm, bvudiv);
      btor_bv_free (d_mm, bve);
    }
    /* e[0] / bve = bvudiv */
    /* bve = 0 and bvudiv < 1...1 */
    for (k = 0; k < 10; k++)
    {
      bve    = btor_bv_new (d_mm, bw);
      tmp    = btor_bv_dec (d_mm, bvmax);
      bvudiv = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, zero, tmp);
      btor_bv_free (d_mm, tmp);
      check_conf_udiv_result (0, udiv, e, bvudiv, bve);
      btor_bv_free (d_mm, bvudiv);
      btor_bv_free (d_mm, bve);
    }
    /* bvudiv = 1...1 and bve > 1 */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      bvudiv = btor_bv_copy (d_mm, bvmax);
      tmp    = btor_bv_uint64_to_bv (d_mm, 2, bw);
      bve    = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, tmp, bvmax);
      btor_bv_free (d_mm, tmp);
      check_conf_udiv_result (0, udiv, e, bvudiv, bve);
      btor_bv_free (d_mm, bvudiv);
      btor_bv_free (d_mm, bve);
    }

    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_btor->slv;
    d_btor->slv = btor_new_sls_solver (d_btor);
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

    goto PROP_INV_CONF_UDIV_TESTS;
  DONE:
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    d_btor->slv->api.delet (d_btor->slv);
    d_btor->slv = slv;

    btor_bv_free (d_mm, bvmax);
    btor_bv_free (d_mm, zero);

    btor_node_release (d_btor, udiv);
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_urem (uint32_t bw)
  {
#ifndef NDEBUG
    (void) bw;
    int32_t k;
    BtorNode *urem, *e[2], *curem, *ce;
    BtorSortId sort;
    BtorBitVector *res, *bve, *bvurem, *bvmax, *zero, *two, *tmp, *tmp2;
    BtorSolver *slv = 0;

    sort = btor_sort_bv (d_btor, bw);
    e[0] = btor_exp_var (d_btor, sort, 0);
    e[1] = btor_exp_var (d_btor, sort, 0);
    btor_sort_release (d_btor, sort);
    urem = btor_exp_bv_urem (d_btor, e[0], e[1]);

    zero  = btor_bv_new (d_mm, bw);
    bvmax = btor_bv_ones (d_mm, bw);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_UREM_TESTS:
    /* bve % e[1] = bvurem */
    /* bvurem = 1...1 and bve < 1...1 */
    bvurem = btor_bv_copy (d_mm, bvmax);
    for (k = 0; k < 10; k++)
    {
      tmp   = btor_bv_dec (d_mm, bvmax);
      bve   = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, zero, tmp);
      ce    = btor_exp_bv_const (d_btor, bve);
      curem = btor_exp_bv_urem (d_btor, ce, e[1]);
      res   = inv_urem_bv (d_btor, urem, bvurem, bve, 1);
      ASSERT_NE (res, nullptr);
      ASSERT_TRUE (btor_bv_is_zero (res));
      btor_bv_free (d_mm, res);
      res = inv_urem_bv (d_btor, curem, bvurem, bve, 1);
      if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      {
        ASSERT_EQ (res, nullptr);
      }
      else
      {
        ASSERT_NE (res, nullptr);
        ASSERT_TRUE (btor_bv_is_zero (res));
        btor_bv_free (d_mm, res);
      }
      btor_node_release (d_btor, curem);
      btor_node_release (d_btor, ce);
      btor_bv_free (d_mm, tmp);
      btor_bv_free (d_mm, bve);
    }
    btor_bv_free (d_mm, bvurem);
    /* bve < bvurem */
    for (k = 0; k < 10; k++)
    {
      tmp    = btor_bv_inc (d_mm, zero);
      bvurem = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, tmp, bvmax);
      btor_bv_free (d_mm, tmp);
      tmp = btor_bv_dec (d_mm, bvurem);
      bve = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, zero, tmp);
      btor_bv_free (d_mm, tmp);
      ce    = btor_exp_bv_const (d_btor, bve);
      curem = btor_exp_bv_urem (d_btor, ce, e[1]);
      res   = inv_urem_bv (d_btor, urem, bvurem, bve, 1);
      ASSERT_NE (res, nullptr);
      btor_bv_free (d_mm, res);
      res = inv_urem_bv (d_btor, curem, bvurem, bve, 1);
      if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      {
        ASSERT_EQ (res, nullptr);
      }
      else
      {
        ASSERT_NE (res, nullptr);
        btor_bv_free (d_mm, res);
      }
      btor_node_release (d_btor, curem);
      btor_node_release (d_btor, ce);
      btor_bv_free (d_mm, bve);
      btor_bv_free (d_mm, bvurem);
    }
    /* bve > bvurem and bve - bvurem <= bvurem -> bve > 2 * bvurem */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      two    = btor_bv_uint64_to_bv (d_mm, 2, bw);
      tmp2   = btor_bv_udiv (d_mm, bvmax, two);
      tmp    = btor_bv_uint64_to_bv (d_mm, 1, bw);
      bvurem = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, tmp, tmp2);
      btor_bv_free (d_mm, tmp);
      btor_bv_free (d_mm, tmp2);
      tmp  = btor_bv_inc (d_mm, bvurem);
      tmp2 = btor_bv_mul (d_mm, bvurem, two);
      bve  = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, tmp, tmp2);
      btor_bv_free (d_mm, tmp);
      btor_bv_free (d_mm, tmp2);
      ce    = btor_exp_bv_const (d_btor, bve);
      curem = btor_exp_bv_urem (d_btor, ce, e[1]);
      res   = inv_urem_bv (d_btor, urem, bvurem, bve, 1);
      ASSERT_NE (res, nullptr);
      btor_bv_free (d_mm, res);
      res = inv_urem_bv (d_btor, curem, bvurem, bve, 1);
      if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      {
        ASSERT_EQ (res, nullptr);
      }
      else
      {
        ASSERT_NE (res, nullptr);
        btor_bv_free (d_mm, res);
      }
      btor_node_release (d_btor, curem);
      btor_node_release (d_btor, ce);
      btor_bv_free (d_mm, two);
      btor_bv_free (d_mm, bvurem);
      btor_bv_free (d_mm, bve);
    }

    /* e[0] % bve = bvurem */
    /* bvurem = 1...1 and bve > 0 */
    bvurem = btor_bv_copy (d_mm, bvmax);
    for (k = 0; k < 10; k++)
    {
      tmp   = btor_bv_inc (d_mm, zero);
      bve   = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, tmp, bvmax);
      ce    = btor_exp_bv_const (d_btor, bve);
      curem = btor_exp_bv_urem (d_btor, e[0], ce);
      res   = inv_urem_bv (d_btor, urem, bvurem, bve, 0);
      ASSERT_NE (res, nullptr);
      ASSERT_TRUE (!btor_bv_compare (res, bvurem));
      btor_bv_free (d_mm, res);
      res = inv_urem_bv (d_btor, curem, bvurem, bve, 0);
      if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      {
        ASSERT_EQ (res, nullptr);
      }
      else
      {
        ASSERT_NE (res, nullptr);
        ASSERT_EQ (btor_bv_compare (res, bvurem), 0);
        btor_bv_free (d_mm, res);
      }
      btor_node_release (d_btor, curem);
      btor_node_release (d_btor, ce);
      btor_bv_free (d_mm, tmp);
      btor_bv_free (d_mm, bve);
    }
    btor_bv_free (d_mm, bvurem);
    /* bve > 0 and bve <= bvurem */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      tmp    = btor_bv_inc (d_mm, zero);
      bvurem = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, tmp, bvmax);
      bve    = btor_bv_new_random_range (d_mm, &d_btor->rng, bw, tmp, bvurem);
      ce     = btor_exp_bv_const (d_btor, bve);
      curem  = btor_exp_bv_urem (d_btor, e[0], ce);
      res    = inv_urem_bv (d_btor, urem, bvurem, bve, 0);
      ASSERT_NE (res, nullptr);
      btor_bv_free (d_mm, res);
      res = inv_urem_bv (d_btor, curem, bvurem, bve, 0);
      if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      {
        ASSERT_EQ (res, nullptr);
      }
      else
      {
        ASSERT_NE (res, nullptr);
        btor_bv_free (d_mm, res);
      }
      btor_node_release (d_btor, curem);
      btor_node_release (d_btor, ce);
      btor_bv_free (d_mm, tmp);
      btor_bv_free (d_mm, bvurem);
      btor_bv_free (d_mm, bve);
    }

    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_btor->slv;
    d_btor->slv = btor_new_sls_solver (d_btor);
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

    goto PROP_INV_CONF_UREM_TESTS;

  DONE:
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    d_btor->slv->api.delet (d_btor->slv);
    d_btor->slv = slv;

    btor_bv_free (d_mm, zero);
    btor_bv_free (d_mm, bvmax);
    btor_node_release (d_btor, urem);
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_concat (uint32_t bw)
  {
#ifndef NDEBUG
    (void) bw;
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
      bws[0]   = btor_rng_pick_rand (&d_btor->rng, 1, bw - 1);
      bws[1]   = bw - bws[0];
      sorts[0] = btor_sort_bv (d_btor, bw);
      sorts[1] = btor_sort_bv (d_btor, bw);
      e[0]     = btor_exp_var (d_btor, sorts[0], 0);
      e[1]     = btor_exp_var (d_btor, sorts[1], 0);
      concat   = btor_exp_bv_concat (d_btor, e[0], e[1]);
      bvconcat = btor_bv_new_random (d_mm, &d_btor->rng, bw);
      for (j = 0; j < 2; j++)
      {
        bve[j] = btor_bv_slice (
            d_mm, bvconcat, j ? bws[1] - 1 : bw - 1, j ? 0 : bws[1]);
        ASSERT_EQ (btor_bv_get_width (bve[j]), bws[j]);
        tmp[j] = btor_bv_copy (d_mm, bve[j]);
        cnt    = 0;
        while (!cnt)
        {
          for (i = 0; i < bws[j]; i++)
          {
            if (btor_rng_pick_rand (&d_btor->rng, 0, 5))
            {
              btor_bv_set_bit (bve[j], i, btor_bv_get_bit (bve[j], i) ? 0 : 1);
              cnt += 1;
            }
          }
        }
      }
      ce[0]      = btor_exp_bv_const (d_btor, bve[0]);
      ce[1]      = btor_exp_bv_const (d_btor, bve[1]);
      cconcat[0] = btor_exp_bv_concat (d_btor, ce[0], e[1]);
      cconcat[1] = btor_exp_bv_concat (d_btor, e[0], ce[1]);
      for (j = 0; j < 2; j++)
      {
        res = inv_concat_bv (d_btor, concat, bvconcat, bve[j ? 0 : 1], j);
        ASSERT_NE (res, nullptr);
        ASSERT_EQ (btor_bv_compare (res, tmp[j]), 0);
        btor_bv_free (d_mm, res);
        res = inv_concat_bv (
            d_btor, cconcat[j ? 0 : 1], bvconcat, bve[j ? 0 : 1], j);
        if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
        {
          ASSERT_EQ (res, nullptr);
        }
        else
        {
          ASSERT_NE (res, nullptr);
          ASSERT_EQ (btor_bv_compare (res, tmp[j]), 0);
          btor_bv_free (d_mm, res);
        }
      }
      for (j = 0; j < 2; j++)
      {
        btor_sort_release (d_btor, sorts[j]);
        btor_node_release (d_btor, cconcat[j]);
        btor_node_release (d_btor, ce[j]);
        btor_node_release (d_btor, e[j]);
        btor_bv_free (d_mm, bve[j]);
        btor_bv_free (d_mm, tmp[j]);
      }

      btor_node_release (d_btor, concat);
      btor_bv_free (d_mm, bvconcat);
    }

    if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_btor->slv;
    d_btor->slv = btor_new_sls_solver (d_btor);
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);

    goto PROP_INV_CONF_CONCAT_TESTS;

  DONE:
    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    d_btor->slv->api.delet (d_btor->slv);
    d_btor->slv = slv;
#else
    (void) bw;
#endif
  }

  BtorMemMgr *d_mm = nullptr;
  BtorRNG *d_rng   = nullptr;

 private:
  void check_conf_mul_result (BtorNode *mul,
                              BtorNode **e,
                              BtorBitVector *bvmul,
                              BtorBitVector *bve)
  {
#ifndef NDEBUG
    BtorNode *cmul[2], *ce[2];
    BtorBitVector *res;

    ce[0]   = btor_exp_bv_const (d_btor, bve);
    ce[1]   = btor_exp_bv_const (d_btor, bve);
    cmul[0] = btor_exp_bv_mul (d_btor, ce[0], e[1]);
    cmul[1] = btor_exp_bv_mul (d_btor, e[0], ce[1]);
    res     = inv_mul_bv (d_btor, mul, bvmul, bve, 0);
    ASSERT_NE (res, nullptr);
    btor_bv_free (d_mm, res);
    res = inv_mul_bv (d_btor, mul, bvmul, bve, 1);
    ASSERT_NE (res, nullptr);
    btor_bv_free (d_mm, res);
    res = inv_mul_bv (d_btor, cmul[1], bvmul, bve, 0);
    ASSERT_TRUE (
        (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS && !res)
        || (btor_opt_get (d_btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_SLS && res));
    if (res)
    {
      if (btor_bv_get_bit (bvmul, 0))
      {
        ASSERT_EQ (btor_bv_get_bit (res, 0), 1u);
      }
      btor_bv_free (d_mm, res);
    }
    res = inv_mul_bv (d_btor, cmul[0], bvmul, bve, 1);
    ASSERT_TRUE (
        (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS && !res)
        || (btor_opt_get (d_btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_SLS && res));
    if (res)
    {
      if (btor_bv_get_bit (bvmul, 0))
      {
        ASSERT_EQ (btor_bv_get_bit (res, 0), 1u);
      }
      btor_bv_free (d_mm, res);
    }
    btor_node_release (d_btor, ce[0]);
    btor_node_release (d_btor, ce[1]);
    btor_node_release (d_btor, cmul[0]);
    btor_node_release (d_btor, cmul[1]);
#else
    (void) mul;
    (void) e;
    (void) bvmul;
    (void) bve;
#endif
  }

  void check_conf_udiv_result (uint32_t eidx,
                               BtorNode *udiv,
                               BtorNode **e,
                               BtorBitVector *bvudiv,
                               BtorBitVector *bve)
  {
#ifndef NDEBUG
    BtorNode *cudiv, *ce;
    BtorBitVector *res;

    if (eidx)
    {
      ce    = btor_exp_bv_const (d_btor, bve);
      cudiv = btor_exp_bv_udiv (d_btor, ce, e[1]);
      res   = inv_udiv_bv (d_btor, udiv, bvudiv, bve, 1);
      ASSERT_NE (res, nullptr);
      ASSERT_FALSE (btor_bv_is_umulo (d_mm, res, bvudiv));
      btor_bv_free (d_mm, res);
      res = inv_udiv_bv (d_btor, cudiv, bvudiv, bve, 1);
      if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      {
        ASSERT_EQ (res, nullptr);
      }
      else
      {
        ASSERT_NE (res, nullptr);
        ASSERT_FALSE (btor_bv_is_umulo (d_mm, res, bvudiv));
        btor_bv_free (d_mm, res);
      }
      btor_node_release (d_btor, cudiv);
      btor_node_release (d_btor, ce);
    }
    else
    {
      ce    = btor_exp_bv_const (d_btor, bve);
      cudiv = btor_exp_bv_udiv (d_btor, e[0], ce);
      res   = inv_udiv_bv (d_btor, udiv, bvudiv, bve, 0);
      ASSERT_NE (res, nullptr);
      btor_bv_free (d_mm, res);
      res = inv_udiv_bv (d_btor, cudiv, bvudiv, bve, 0);
      ASSERT_TRUE (
          (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS && !res)
          || (btor_opt_get (d_btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_SLS
              && res));
      if (res) btor_bv_free (d_mm, res);
      btor_node_release (d_btor, cudiv);
      btor_node_release (d_btor, ce);
    }
#else
    (void) eidx;
    (void) udiv;
    (void) e;
    (void) bvudiv;
    (void) bve;
#endif
  }

  void check_conf_shift (uint32_t eidx,
                         BtorNode *shift,
                         BtorNode **e,
                         BtorNode *(*exp_fun) (Btor *, BtorNode *, BtorNode *),
                         BtorBitVector *(*inv_fun) (Btor *,
                                                    BtorNode *,
                                                    BtorBitVector *,
                                                    BtorBitVector *,
                                                    int32_t eidx),
                         const char *ve,
                         const char *vshift,
                         uint64_t rvalmax)
  {
#ifndef NDEBUG
    BtorNode *cshift, *ce;
    BtorBitVector *res, *bvshift, *bve;

    bve     = btor_bv_char_to_bv (d_mm, ve);
    bvshift = btor_bv_char_to_bv (d_mm, vshift);
    ce      = btor_exp_bv_const (d_btor, bve);
    if (eidx)
    {
      cshift = exp_fun (d_btor, ce, e[1]);
      res    = inv_fun (d_btor, shift, bvshift, bve, 1);
      ASSERT_NE (res, nullptr);
      ASSERT_LE (btor_bv_to_uint64 (res), rvalmax);
      btor_bv_free (d_mm, res);
      res = inv_fun (d_btor, cshift, bvshift, bve, 1);
      if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      {
        ASSERT_EQ (res, nullptr);
      }
      else
      {
        ASSERT_NE (res, nullptr);
        ASSERT_LE (btor_bv_to_uint64 (res), rvalmax);
        btor_bv_free (d_mm, res);
      }
    }
    else
    {
      cshift = exp_fun (d_btor, e[0], ce);
      res    = inv_fun (d_btor, shift, bvshift, bve, 0);
      ASSERT_NE (res, nullptr);
      btor_bv_free (d_mm, res);
      res = inv_fun (d_btor, cshift, bvshift, bve, 0);
      if (btor_opt_get (d_btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS)
      {
        ASSERT_EQ (res, nullptr);
      }
      else
      {
        ASSERT_NE (res, nullptr);
        btor_bv_free (d_mm, res);
      }
    }
    btor_bv_free (d_mm, bvshift);
    btor_bv_free (d_mm, bve);
    btor_node_release (d_btor, ce);
    btor_node_release (d_btor, cshift);
#else
    (void) eidx;
    (void) shift;
    (void) e;
    (void) exp_fun;
    (void) inv_fun;
    (void) ve;
    (void) vshift;
    (void) rvalmax;
#endif
  }
};

TEST_F (TestPropInv, complete_add)
{
#ifndef NDEBUG
  check_binary (btor_exp_bv_add, btor_bv_add, inv_add_bv);
#endif
}

TEST_F (TestPropInv, complete_and)
{
#ifndef NDEBUG
  check_binary (btor_exp_bv_and, btor_bv_and, inv_and_bv);
#endif
}

TEST_F (TestPropInv, complete_eq)
{
#ifndef NDEBUG
  check_binary (btor_exp_eq, btor_bv_eq, inv_eq_bv);
#endif
}

TEST_F (TestPropInv, complete_ult)
{
#ifndef NDEBUG
  check_binary (btor_exp_bv_ult, btor_bv_ult, inv_ult_bv);
#endif
}

TEST_F (TestPropInv, complete_sll)
{
#ifndef NDEBUG
  check_shift (btor_exp_bv_sll, btor_bv_sll, inv_sll_bv);
#endif
}

TEST_F (TestPropInv, complete_srl)
{
#ifndef NDEBUG
  check_shift (btor_exp_bv_srl, btor_bv_srl, inv_srl_bv);
#endif
}

TEST_F (TestPropInv, complete_mul)
{
#ifndef NDEBUG
  check_binary (btor_exp_bv_mul, btor_bv_mul, inv_mul_bv);
#endif
}

TEST_F (TestPropInv, complete_udiv)
{
#ifndef NDEBUG
  check_binary (btor_exp_bv_udiv, btor_bv_udiv, inv_udiv_bv);
#endif
}

TEST_F (TestPropInv, complete_urem)
{
#ifndef NDEBUG
  check_binary (btor_exp_bv_urem, btor_bv_urem, inv_urem_bv);
#endif
}

TEST_F (TestPropInv, complete_concat)
{
#ifndef NDEBUG
  check_binary (btor_exp_bv_concat, btor_bv_concat, inv_concat_bv);
#endif
}

TEST_F (TestPropInv, complete_slice)
{
#ifndef NDEBUG
  uint32_t bw;
  uint64_t up, lo, i, k;
  BtorNode *exp, *e;
  BtorBitVector *bve, *bvexp, *res;
  BtorSortId sort;

  bw   = TEST_PROP_INV_COMPLETE_BW;
  sort = btor_sort_bv (d_btor, bw);
  e    = btor_exp_var (d_btor, sort, 0);
  btor_sort_release (d_btor, sort);

  for (lo = 0; lo < bw; lo++)
  {
    for (up = lo; up < bw; up++)
    {
      exp = btor_exp_bv_slice (d_btor, e, up, lo);
      for (i = 0; i < (uint32_t) (1 << bw); i++)
      {
        bve   = btor_bv_uint64_to_bv (d_mm, i, bw);
        bvexp = btor_bv_slice (d_mm, bve, up, lo);
        for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
        {
          res = inv_slice_bv (d_btor, exp, bvexp, bve, 0);
          ASSERT_NE (res, nullptr);
          if (!btor_bv_compare (res, bve)) break;
          btor_bv_free (d_mm, res);
          res = 0;
        }
        ASSERT_NE (res, nullptr);
        ASSERT_EQ (btor_bv_compare (res, bve), 0);
        btor_bv_free (d_mm, res);
        btor_bv_free (d_mm, bvexp);
        btor_bv_free (d_mm, bve);
      }
      btor_node_release (d_btor, exp);
    }
  }
  btor_node_release (d_btor, e);
#endif
}

TEST_F (TestPropInv, conf_and)
{
  check_conf_and (1);
  check_conf_and (4);
  check_conf_and (8);
}

TEST_F (TestPropInv, conf_ult)
{
  check_conf_ult (1);
  check_conf_ult (4);
  check_conf_ult (8);
}

TEST_F (TestPropInv, conf_sll)
{
  check_conf_sll (2);
  check_conf_sll (4);
  check_conf_sll (8);
}

TEST_F (TestPropInv, conf_srl)
{
  check_conf_srl (2);
  check_conf_srl (4);
  check_conf_srl (8);
}

TEST_F (TestPropInv, conf_mul)
{
  check_conf_mul (1);
  check_conf_mul (4);
  check_conf_mul (8);
}

TEST_F (TestPropInv, conf_udiv)
{
  check_conf_udiv (1);
  check_conf_udiv (4);
  check_conf_udiv (8);
}

TEST_F (TestPropInv, conf_urem)
{
  check_conf_urem (1);
  check_conf_urem (4);
  check_conf_urem (8);
}

TEST_F (TestPropInv, conf_concat)
{
  check_conf_concat (2);
  check_conf_concat (4);
  check_conf_concat (8);
}

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
#include "btormodel.h"
#include "btornode.h"
#include "btorproputils.h"
#include "utils/btorutil.h"
}

class TestProp : public TestBtor
{
 protected:
  static constexpr int32_t TEST_PROP_COMPLETE_BW      = 4;
  static constexpr int32_t TEST_PROP_COMPLETE_N_TESTS = 1000;

  void SetUp () override
  {
    TestBtor::SetUp ();
    d_btor->slv       = btor_new_prop_solver (d_btor);
    d_btor->slv->btor = d_btor;
    d_mm              = d_btor->mm;
    d_rng             = &d_btor->rng;

    btor_opt_set (d_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_USE_INV_VALUE, 1000);
    btor_opt_set (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
    btor_opt_set (d_btor, BTOR_OPT_SORT_EXP, 0);
    btor_opt_set (d_btor, BTOR_OPT_INCREMENTAL, 1);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_CONC_FLIP, 0);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_SLICE_FLIP, 0);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_EQ_FLIP, 0);
    btor_opt_set (d_btor, BTOR_OPT_PROP_PROB_AND_FLIP, 0);
    // btor_opt_set (d_btor, BTOR_OPT_LOGLEVEL, 2);
  }

  BtorMemMgr *d_mm = nullptr;
  BtorRNG *d_rng   = nullptr;

  void prop_complete_binary_eidx (
      uint32_t n,
      int32_t eidx,
      uint32_t bw,
      BtorBitVector *bve,
      BtorBitVector *bvres,
      BtorBitVector *bvexp,
      BtorNode *(*create_exp) (Btor *, BtorNode *, BtorNode *),
      BtorBitVector *(*create_bv) (BtorMemMgr *,
                                   const BtorBitVector *,
                                   const BtorBitVector *),
      BtorBitVector *(*inv_bv) (
          Btor *, BtorNode *, BtorBitVector *, BtorBitVector *, int32_t))
  {
#ifndef NDEBUG
    int32_t i, idx, sat_res;
    BtorNode *e[2], *exp, *val, *eq;
    BtorBitVector *bvetmp[2], *bvexptmp, *res[2], *tmp;
    BtorSortId sort;

    sort  = btor_sort_bv (d_btor, bw);
    e[0]  = btor_exp_var (d_btor, sort, 0);
    e[1]  = btor_exp_var (d_btor, sort, 0);
    exp   = create_exp (d_btor, e[0], e[1]);
    val   = btor_exp_bv_const (d_btor, bvexp);
    eq    = btor_exp_eq (d_btor, exp, val);

    idx = eidx ? 0 : 1;

    bvetmp[eidx] = btor_bv_new_random (d_mm, d_rng, bw);
    bvetmp[idx]  = n == 1 ? btor_bv_copy (d_mm, bve)
                         : btor_bv_new_random (d_mm, d_rng, bw);
    bvexptmp = create_bv (d_mm, bvetmp[0], bvetmp[1]);

    /* init bv model */
    btor_model_init_bv (d_btor, &d_btor->bv_model);
    btor_model_init_fun (d_btor, &d_btor->fun_model);
    btor_model_add_to_bv (d_btor, d_btor->bv_model, e[idx], bvetmp[idx]);
    btor_model_add_to_bv (d_btor, d_btor->bv_model, e[eidx], bvetmp[eidx]);
    btor_model_add_to_bv (d_btor, d_btor->bv_model, exp, bvexptmp);

    // printf ("eidx %d bvetmp[0] %s bvetmp[1] %s\n", eidx, btor_bv_to_char
    // (d_mm, bvetmp[0]), btor_bv_to_char (d_mm, bvetmp[1]));
    /* -> first test local completeness  */
    /* we must find a solution within n move(s) */
    res[eidx] = inv_bv (d_btor, exp, bvexp, bve, eidx);
    ASSERT_NE (res[eidx], nullptr);
    res[idx] = n == 1 ? btor_bv_copy (d_mm, bve)
                      : inv_bv (d_btor, exp, bvexp, res[eidx], idx);
    ASSERT_NE (res[idx], nullptr);
    /* Note: this is also tested within the inverse function(s) */
    tmp = create_bv (d_mm, res[0], res[1]);
    ASSERT_EQ (btor_bv_compare (tmp, bvexp), 0);
    btor_bv_free (d_mm, tmp);
    btor_bv_free (d_mm, res[0]);
    btor_bv_free (d_mm, res[1]);
    /* try to find the exact given solution */
    if (n == 1)
    {
      for (i = 0, res[eidx] = 0; i < TEST_PROP_COMPLETE_N_TESTS; i++)
      {
        res[eidx] = inv_bv (d_btor, exp, bvexp, bve, eidx);
        ASSERT_NE (res[eidx], nullptr);
        if (!btor_bv_compare (res[eidx], bvres)) break;
        btor_bv_free (d_mm, res[eidx]);
        res[eidx] = nullptr;
      }
      ASSERT_NE (res[eidx], nullptr);
      ASSERT_EQ (btor_bv_compare (res[eidx], bvres), 0);
      btor_bv_free (d_mm, res[eidx]);
    }

    /* -> then test completeness of the whole propagation algorithm
     *    (we must find a solution within n move(s)) */
    ((BtorPropSolver *) d_btor->slv)->stats.moves = 0;
    btor_assume_exp (d_btor, eq);
    btor_model_init_bv (d_btor, &d_btor->bv_model);
    btor_model_init_fun (d_btor, &d_btor->fun_model);
    btor_model_add_to_bv (d_btor, d_btor->bv_model, e[idx], bvetmp[idx]);
    btor_model_add_to_bv (d_btor, d_btor->bv_model, e[eidx], bvetmp[eidx]);
    btor_model_add_to_bv (d_btor, d_btor->bv_model, exp, bvexptmp);
    btor_bv_free (d_mm, bvetmp[0]);
    btor_bv_free (d_mm, bvetmp[1]);
    btor_bv_free (d_mm, bvexptmp);
    btor_node_release (d_btor, eq);
    btor_node_release (d_btor, val);
    btor_node_release (d_btor, exp);
    btor_node_release (d_btor, e[0]);
    btor_node_release (d_btor, e[1]);
    btor_sort_release (d_btor, sort);
    sat_res = sat_prop_solver_aux (d_btor);
    ASSERT_EQ (sat_res, BTOR_RESULT_SAT);
    ASSERT_LE (((BtorPropSolver *) d_btor->slv)->stats.moves, n);
    btor_reset_incremental_usage (d_btor);
#else
    (void) n;
    (void) eidx;
    (void) bw;
    (void) bve;
    (void) bvres;
    (void) bvexp;
    (void) create_exp;
    (void) create_bv;
    (void) inv_bv;
#endif
  }

  void prop_complete_binary (
      uint32_t n,
      BtorNode *(*create_exp) (Btor *, BtorNode *, BtorNode *),
      BtorBitVector *(*create_bv) (BtorMemMgr *,
                                   const BtorBitVector *,
                                   const BtorBitVector *),
      BtorBitVector *(*inv_bv) (
          Btor *, BtorNode *, BtorBitVector *, BtorBitVector *, int32_t))
  {
    uint32_t bw;
    uint64_t i, j, k;
    BtorBitVector *bve[2], *bvexp;

    bw = TEST_PROP_COMPLETE_BW;

    for (i = 0; i < (uint32_t) (1 << bw); i++)
    {
      bve[0] = btor_bv_uint64_to_bv (d_mm, i, bw);
      for (j = 0; j < (uint32_t) (1 << bw); j++)
      {
        bve[1] = btor_bv_uint64_to_bv (d_mm, j, bw);
        bvexp  = create_bv (d_mm, bve[0], bve[1]);
        // printf ("bve[0] %s bve[1] %s bvexp %s\n", btor_bv_to_char (d_mm,
        // bve[0]), btor_bv_to_char (d_mm, bve[1]), btor_bv_to_char (d_mm,
        // bvexp));
        /* -> first test local completeness  */
        for (k = 0; k < bw; k++)
        {
          prop_complete_binary_eidx (
              n, 1, bw, bve[0], bve[1], bvexp, create_exp, create_bv, inv_bv);
          prop_complete_binary_eidx (
              n, 0, bw, bve[1], bve[0], bvexp, create_exp, create_bv, inv_bv);
        }
        btor_bv_free (d_mm, bve[1]);
        btor_bv_free (d_mm, bvexp);
      }
      btor_bv_free (d_mm, bve[0]);
    }
  }
};

/*------------------------------------------------------------------------*/

TEST_F (TestProp, one_complete_add)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_add, btor_bv_add, inv_add_bv);
#endif
}

TEST_F (TestProp, one_complete_and)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_and, btor_bv_and, inv_and_bv);
#endif
}

TEST_F (TestProp, one_complete_eq)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_eq, btor_bv_eq, inv_eq_bv);
#endif
}

TEST_F (TestProp, one_complete_ult)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_ult, btor_bv_ult, inv_ult_bv);
#endif
}

TEST_F (TestProp, one_complete_sll)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_sll, btor_bv_sll, inv_sll_bv);
#endif
}

TEST_F (TestProp, one_complete_srl)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_srl, btor_bv_srl, inv_srl_bv);
#endif
}

TEST_F (TestProp, one_complete_mul)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_mul, btor_bv_mul, inv_mul_bv);
#endif
}

TEST_F (TestProp, one_complete_udiv)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_udiv, btor_bv_udiv, inv_udiv_bv);
#endif
}

TEST_F (TestProp, one_complete_urem)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_urem, btor_bv_urem, inv_urem_bv);
#endif
}

TEST_F (TestProp, one_complete_concat)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_concat, btor_bv_concat, inv_concat_bv);
#endif
}

/*------------------------------------------------------------------------*/

TEST_F (TestProp, complete_add)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_add, btor_bv_add, inv_add_bv);
#endif
}

TEST_F (TestProp, complete_and)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_and, btor_bv_and, inv_and_bv);
#endif
}

TEST_F (TestProp, complete_eq)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_eq, btor_bv_eq, inv_eq_bv);
#endif
}

TEST_F (TestProp, complete_ult)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_ult, btor_bv_ult, inv_ult_bv);
#endif
}

TEST_F (TestProp, complete_sll)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_sll, btor_bv_sll, inv_sll_bv);
#endif
}

TEST_F (TestProp, complete_srl)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_srl, btor_bv_srl, inv_srl_bv);
#endif
}

TEST_F (TestProp, complete_mul)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_mul, btor_bv_mul, inv_mul_bv);
#endif
}

TEST_F (TestProp, complete_udiv)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_udiv, btor_bv_udiv, inv_udiv_bv);
#endif
}

TEST_F (TestProp, complete_urem)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_urem, btor_bv_urem, inv_urem_bv);
#endif
}

TEST_F (TestProp, complete_concat)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_concat, btor_bv_concat, inv_concat_bv);
#endif
}

TEST_F (TestProp, complete_slice)
{
#ifndef NDEBUG
  int32_t sat_res;
  uint32_t bw;
  uint64_t up, lo, i, j, k;
  BtorNode *exp, *e, *val, *eq;
  BtorBitVector *bve, *bvexp, *bvetmp, *bvexptmp, *res, *tmp;
  BtorSortId sort;

  bw   = TEST_PROP_COMPLETE_BW;
  sort = btor_sort_bv (d_btor, bw);

  for (lo = 0; lo < bw; lo++)
  {
    for (up = lo; up < bw; up++)
    {
      for (i = 0; i < (uint32_t) (1 << bw); i++)
      {
        for (j = 0; j < bw; j++)
        {
          e        = btor_exp_var (d_btor, sort, 0);
          exp      = btor_exp_bv_slice (d_btor, e, up, lo);
          bve      = btor_bv_uint64_to_bv (d_mm, i, bw);
          bvexp    = btor_bv_slice (d_mm, bve, up, lo);
          val      = btor_exp_bv_const (d_btor, bvexp);
          eq       = btor_exp_eq (d_btor, exp, val);
          bvetmp   = btor_bv_new_random (d_mm, d_rng, bw);
          bvexptmp = btor_bv_slice (d_mm, bvetmp, up, lo);
          /* init bv model */
          btor_model_init_bv (d_btor, &d_btor->bv_model);
          btor_model_init_fun (d_btor, &d_btor->fun_model);
          btor_model_add_to_bv (d_btor, d_btor->bv_model, e, bvetmp);
          btor_model_add_to_bv (d_btor, d_btor->bv_model, exp, bvexptmp);

          /* -> first test local completeness
           *    we must find a solution within one move */
          res = inv_slice_bv (d_btor, exp, bvexp, bve, 0);
          ASSERT_NE (res, nullptr);
          /* Note: this is also tested within inverse function */
          tmp = btor_bv_slice (d_mm, res, up, lo);
          ASSERT_EQ (btor_bv_compare (tmp, bvexp), 0);
          btor_bv_free (d_mm, tmp);
          btor_bv_free (d_mm, res);
          /* try to find exact given solution */
          for (k = 0, res = 0; k < TEST_PROP_COMPLETE_N_TESTS; k++)
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

          /* -> then test completeness of whole propagation algorithm
           *    (we must find a solution within one move) */
          ((BtorPropSolver *) d_btor->slv)->stats.moves = 0;
          btor_assume_exp (d_btor, eq);
          btor_model_init_bv (d_btor, &d_btor->bv_model);
          btor_model_init_fun (d_btor, &d_btor->fun_model);
          btor_model_add_to_bv (d_btor, d_btor->bv_model, e, bvetmp);
          btor_model_add_to_bv (d_btor, d_btor->bv_model, exp, bvexptmp);
          btor_bv_free (d_mm, bve);
          btor_bv_free (d_mm, bvexp);
          btor_bv_free (d_mm, bvetmp);
          btor_bv_free (d_mm, bvexptmp);
          btor_node_release (d_btor, eq);
          btor_node_release (d_btor, val);
          btor_node_release (d_btor, exp);
          btor_node_release (d_btor, e);
          sat_res = sat_prop_solver_aux (d_btor);
          ASSERT_EQ (sat_res, BTOR_RESULT_SAT);
          ASSERT_LE (((BtorPropSolver *) d_btor->slv)->stats.moves, 1u);
          btor_reset_incremental_usage (d_btor);
        }
      }
    }
  }
  btor_sort_release (d_btor, sort);
#endif
}

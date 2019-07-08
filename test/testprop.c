/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testprop.h"
#include "btorbv.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btormodel.h"
#include "btornode.h"
#include "btorslvpropsls.h"
#include "testrunner.h"
#include "utils/btorutil.h"

static Btor *g_btor;
static BtorMemMgr *g_mm;
static BtorRNG *g_rng;

/*------------------------------------------------------------------------*/

#define TEST_PROP_COMPLETE_BW 4
#define TEST_PROP_COMPLETE_N_TESTS 1000

/*------------------------------------------------------------------------*/

#define TEST_PROP_INIT                                             \
  do                                                               \
  {                                                                \
    g_btor            = btor_new ();                               \
    g_btor->slv       = btor_new_prop_solver (g_btor);             \
    g_btor->slv->btor = g_btor;                                    \
    btor_opt_set (g_btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);      \
    btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_USE_INV_VALUE, 1000); \
    btor_opt_set (g_btor, BTOR_OPT_REWRITE_LEVEL, 0);              \
    btor_opt_set (g_btor, BTOR_OPT_SORT_EXP, 0);                   \
    btor_opt_set (g_btor, BTOR_OPT_INCREMENTAL, 1);                \
    btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_CONC_FLIP, 0);        \
    btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_SLICE_FLIP, 0);       \
    btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_EQ_FLIP, 0);          \
    btor_opt_set (g_btor, BTOR_OPT_PROP_PROB_AND_FLIP, 0);         \
    /*btor_opt_set (g_btor, BTOR_OPT_LOGLEVEL, 2);*/               \
    g_mm  = g_btor->mm;                                            \
    g_rng = &g_btor->rng;                                          \
  } while (0)

#define TEST_PROP_ONE_COMPLETE_BINARY_INIT(fun) \
  do                                            \
  {                                             \
    TEST_PROP_INIT;                             \
    bw0 = bw1 = TEST_PROP_COMPLETE_BW;          \
  } while (0)

#define TEST_PROP_ONE_COMPLETE_BINARY_FINISH(fun) \
  do                                              \
  {                                               \
    btor_delete (g_btor);                         \
  } while (0)

#ifndef NDEBUG
static inline void
prop_complete_binary_eidx (
    uint32_t n,
    int32_t eidx,
    uint32_t bw0,
    uint32_t bw1,
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
  int32_t i, idx, sat_res;
  BtorNode *e[2], *exp, *val, *eq;
  BtorBitVector *bvetmp[2], *bvexptmp, *res[2], *tmp;
  BtorSortId sort0, sort1;

  sort0 = btor_sort_bv (g_btor, bw0);
  sort1 = btor_sort_bv (g_btor, bw1);
  e[0]  = btor_exp_var (g_btor, sort0, 0);
  e[1]  = btor_exp_var (g_btor, sort1, 0);
  exp   = create_exp (g_btor, e[0], e[1]);
  val   = btor_exp_bv_const (g_btor, bvexp);
  eq    = btor_exp_eq (g_btor, exp, val);

  idx = eidx ? 0 : 1;

  bvetmp[eidx] = btor_bv_new_random (g_mm, g_rng, eidx ? bw1 : bw0);
  bvetmp[idx]  = n == 1 ? btor_bv_copy (g_mm, bve)
                       : btor_bv_new_random (g_mm, g_rng, idx ? bw1 : bw0);
  bvexptmp = create_bv (g_mm, bvetmp[0], bvetmp[1]);

  /* init bv model */
  btor_model_init_bv (g_btor, &g_btor->bv_model);
  btor_model_init_fun (g_btor, &g_btor->fun_model);
  btor_model_add_to_bv (g_btor, g_btor->bv_model, e[idx], bvetmp[idx]);
  btor_model_add_to_bv (g_btor, g_btor->bv_model, e[eidx], bvetmp[eidx]);
  btor_model_add_to_bv (g_btor, g_btor->bv_model, exp, bvexptmp);

  // printf ("eidx %d bvetmp[0] %s bvetmp[1] %s\n", eidx, btor_bv_to_char (g_mm,
  // bvetmp[0]), btor_bv_to_char (g_mm, bvetmp[1]));
  /* -> first test local completeness  */
  /* we must find a solution within n move(s) */
  res[eidx] = inv_bv (g_btor, exp, bvexp, bve, eidx);
  assert (res[eidx]);
  res[idx] = n == 1 ? btor_bv_copy (g_mm, bve)
                    : inv_bv (g_btor, exp, bvexp, res[eidx], idx);
  assert (res[idx]);
  /* Note: this is also tested within the inverse function(s) */
  tmp = create_bv (g_mm, res[0], res[1]);
  assert (!btor_bv_compare (tmp, bvexp));
  btor_bv_free (g_mm, tmp);
  btor_bv_free (g_mm, res[0]);
  btor_bv_free (g_mm, res[1]);
  /* try to find the exact given solution */
  if (n == 1)
  {
    for (i = 0, res[eidx] = 0; i < TEST_PROP_COMPLETE_N_TESTS; i++)
    {
      res[eidx] = inv_bv (g_btor, exp, bvexp, bve, eidx);
      assert (res[eidx]);
      if (!btor_bv_compare (res[eidx], bvres)) break;
      btor_bv_free (g_mm, res[eidx]);
      res[eidx] = 0;
    }
    assert (res[eidx]);
    assert (!btor_bv_compare (res[eidx], bvres));
    btor_bv_free (g_mm, res[eidx]);
  }

  /* -> then test completeness of the whole propagation algorithm
   *    (we must find a solution within n move(s)) */
  ((BtorPropSolver *) g_btor->slv)->stats.moves = 0;
  btor_assume_exp (g_btor, eq);
  btor_model_init_bv (g_btor, &g_btor->bv_model);
  btor_model_init_fun (g_btor, &g_btor->fun_model);
  btor_model_add_to_bv (g_btor, g_btor->bv_model, e[idx], bvetmp[idx]);
  btor_model_add_to_bv (g_btor, g_btor->bv_model, e[eidx], bvetmp[eidx]);
  btor_model_add_to_bv (g_btor, g_btor->bv_model, exp, bvexptmp);
  btor_bv_free (g_mm, bvetmp[0]);
  btor_bv_free (g_mm, bvetmp[1]);
  btor_bv_free (g_mm, bvexptmp);
  btor_node_release (g_btor, eq);
  btor_node_release (g_btor, val);
  btor_node_release (g_btor, exp);
  btor_node_release (g_btor, e[0]);
  btor_node_release (g_btor, e[1]);
  btor_sort_release (g_btor, sort0);
  btor_sort_release (g_btor, sort1);
  sat_res = sat_prop_solver_aux (g_btor);
  assert (sat_res == BTOR_RESULT_SAT);
  assert (((BtorPropSolver *) g_btor->slv)->stats.moves <= n);
  btor_reset_incremental_usage (g_btor);
}

static void
prop_complete_binary (uint32_t n,
                      BtorNode *(*create_exp) (Btor *, BtorNode *, BtorNode *),
                      BtorBitVector *(*create_bv) (BtorMemMgr *,
                                                   const BtorBitVector *,
                                                   const BtorBitVector *),
                      BtorBitVector *(*inv_bv) (Btor *,
                                                BtorNode *,
                                                BtorBitVector *,
                                                BtorBitVector *,
                                                int32_t))
{
  uint32_t bw0, bw1;
  uint64_t i, j, k;
  BtorBitVector *bve[2], *bvexp;

  TEST_PROP_ONE_COMPLETE_BINARY_INIT (create_exp);
  if (create_exp == btor_exp_bv_sll || create_exp == btor_exp_bv_srl)
    bw1 = btor_util_log_2 (bw0);

  for (i = 0; i < (uint32_t) (1 << bw0); i++)
  {
    bve[0] = btor_bv_uint64_to_bv (g_mm, i, bw0);
    for (j = 0; j < (uint32_t) (1 << bw1); j++)
    {
      bve[1] = btor_bv_uint64_to_bv (g_mm, j, bw1);
      bvexp  = create_bv (g_mm, bve[0], bve[1]);
      // printf ("bve[0] %s bve[1] %s bvexp %s\n", btor_bv_to_char (g_mm,
      // bve[0]), btor_bv_to_char (g_mm, bve[1]), btor_bv_to_char (g_mm,
      // bvexp));
      /* -> first test local completeness  */
      for (k = 0; k < bw0; k++)
      {
        prop_complete_binary_eidx (n,
                                   1,
                                   bw0,
                                   bw1,
                                   bve[0],
                                   bve[1],
                                   bvexp,
                                   create_exp,
                                   create_bv,
                                   inv_bv);
        prop_complete_binary_eidx (n,
                                   0,
                                   bw0,
                                   bw1,
                                   bve[1],
                                   bve[0],
                                   bvexp,
                                   create_exp,
                                   create_bv,
                                   inv_bv);
      }
      btor_bv_free (g_mm, bve[1]);
      btor_bv_free (g_mm, bvexp);
    }
    btor_bv_free (g_mm, bve[0]);
  }

  TEST_PROP_ONE_COMPLETE_BINARY_FINISH (fun);
}
#endif

/*------------------------------------------------------------------------*/

static void
test_prop_one_complete_add_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_add, btor_bv_add, inv_add_bv);
#endif
}

static void
test_prop_one_complete_and_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_and, btor_bv_and, inv_and_bv);
#endif
}

static void
test_prop_one_complete_eq_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_eq, btor_bv_eq, inv_eq_bv);
#endif
}

static void
test_prop_one_complete_ult_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_ult, btor_bv_ult, inv_ult_bv);
#endif
}

static void
test_prop_one_complete_sll_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_sll, btor_bv_sll, inv_sll_bv);
#endif
}

static void
test_prop_one_complete_srl_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_srl, btor_bv_srl, inv_srl_bv);
#endif
}

static void
test_prop_one_complete_mul_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_mul, btor_bv_mul, inv_mul_bv);
#endif
}

static void
test_prop_one_complete_udiv_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_udiv, btor_bv_udiv, inv_udiv_bv);
#endif
}

static void
test_prop_one_complete_urem_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_urem, btor_bv_urem, inv_urem_bv);
#endif
}

static void
test_prop_one_complete_concat_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (1, btor_exp_bv_concat, btor_bv_concat, inv_concat_bv);
#endif
}

/*------------------------------------------------------------------------*/

static void
test_prop_complete_add_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_add, btor_bv_add, inv_add_bv);
#endif
}

static void
test_prop_complete_and_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_and, btor_bv_and, inv_and_bv);
#endif
}

static void
test_prop_complete_eq_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_eq, btor_bv_eq, inv_eq_bv);
#endif
}

static void
test_prop_complete_ult_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_ult, btor_bv_ult, inv_ult_bv);
#endif
}

static void
test_prop_complete_sll_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_sll, btor_bv_sll, inv_sll_bv);
#endif
}

static void
test_prop_complete_srl_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_srl, btor_bv_srl, inv_srl_bv);
#endif
}

static void
test_prop_complete_mul_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_mul, btor_bv_mul, inv_mul_bv);
#endif
}

static void
test_prop_complete_udiv_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_udiv, btor_bv_udiv, inv_udiv_bv);
#endif
}

static void
test_prop_complete_urem_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_urem, btor_bv_urem, inv_urem_bv);
#endif
}

static void
test_prop_complete_concat_bv (void)
{
#ifndef NDEBUG
  prop_complete_binary (2, btor_exp_bv_concat, btor_bv_concat, inv_concat_bv);
#endif
}

static void
test_prop_complete_slice_bv (void)
{
#ifndef NDEBUG
  int32_t sat_res;
  uint32_t bw;
  uint64_t up, lo, i, j, k;
  BtorNode *exp, *e, *val, *eq;
  BtorBitVector *bve, *bvexp, *bvetmp, *bvexptmp, *res, *tmp;
  BtorSortId sort;

  TEST_PROP_INIT;
  bw   = TEST_PROP_COMPLETE_BW;
  sort = btor_sort_bv (g_btor, bw);

  for (lo = 0; lo < bw; lo++)
  {
    for (up = lo; up < bw; up++)
    {
      for (i = 0; i < (uint32_t) (1 << bw); i++)
      {
        for (j = 0; j < bw; j++)
        {
          e        = btor_exp_var (g_btor, sort, 0);
          exp      = btor_exp_bv_slice (g_btor, e, up, lo);
          bve      = btor_bv_uint64_to_bv (g_mm, i, bw);
          bvexp    = btor_bv_slice (g_mm, bve, up, lo);
          val      = btor_exp_bv_const (g_btor, bvexp);
          eq       = btor_exp_eq (g_btor, exp, val);
          bvetmp   = btor_bv_new_random (g_mm, g_rng, bw);
          bvexptmp = btor_bv_slice (g_mm, bvetmp, up, lo);
          /* init bv model */
          btor_model_init_bv (g_btor, &g_btor->bv_model);
          btor_model_init_fun (g_btor, &g_btor->fun_model);
          btor_model_add_to_bv (g_btor, g_btor->bv_model, e, bvetmp);
          btor_model_add_to_bv (g_btor, g_btor->bv_model, exp, bvexptmp);

          /* -> first test local completeness
           *    we must find a solution within one move */
          res = inv_slice_bv (g_btor, exp, bvexp, bve, 0);
          assert (res);
          /* Note: this is also tested within inverse function */
          tmp = btor_bv_slice (g_mm, res, up, lo);
          assert (!btor_bv_compare (tmp, bvexp));
          btor_bv_free (g_mm, tmp);
          btor_bv_free (g_mm, res);
          /* try to find exact given solution */
          for (k = 0, res = 0; k < TEST_PROP_COMPLETE_N_TESTS; k++)
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

          /* -> then test completeness of whole propagation algorithm
           *    (we must find a solution within one move) */
          ((BtorPropSolver *) g_btor->slv)->stats.moves = 0;
          btor_assume_exp (g_btor, eq);
          btor_model_init_bv (g_btor, &g_btor->bv_model);
          btor_model_init_fun (g_btor, &g_btor->fun_model);
          btor_model_add_to_bv (g_btor, g_btor->bv_model, e, bvetmp);
          btor_model_add_to_bv (g_btor, g_btor->bv_model, exp, bvexptmp);
          btor_bv_free (g_mm, bve);
          btor_bv_free (g_mm, bvexp);
          btor_bv_free (g_mm, bvetmp);
          btor_bv_free (g_mm, bvexptmp);
          btor_node_release (g_btor, eq);
          btor_node_release (g_btor, val);
          btor_node_release (g_btor, exp);
          btor_node_release (g_btor, e);
          sat_res = sat_prop_solver_aux (g_btor);
          assert (sat_res == BTOR_RESULT_SAT);
          assert (((BtorPropSolver *) g_btor->slv)->stats.moves <= 1);
          btor_reset_incremental_usage (g_btor);
        }
      }
    }
  }
  btor_sort_release (g_btor, sort);
  btor_delete (g_btor);
#endif
}

/*------------------------------------------------------------------------*/

void
init_prop_tests (void)
{
}

void
run_prop_tests (int32_t argc, char **argv)
{
  (void) argc;
  (void) argv;
  (void) g_btor;
  (void) g_mm;
  (void) g_rng;
  BTOR_RUN_TEST (prop_one_complete_add_bv);
  BTOR_RUN_TEST (prop_one_complete_and_bv);
  BTOR_RUN_TEST (prop_one_complete_eq_bv);
  BTOR_RUN_TEST (prop_one_complete_ult_bv);
  BTOR_RUN_TEST (prop_one_complete_sll_bv);
  BTOR_RUN_TEST (prop_one_complete_srl_bv);
  BTOR_RUN_TEST (prop_one_complete_mul_bv);
  BTOR_RUN_TEST (prop_one_complete_udiv_bv);
  BTOR_RUN_TEST (prop_one_complete_urem_bv);
  BTOR_RUN_TEST (prop_one_complete_concat_bv);

  BTOR_RUN_TEST (prop_complete_add_bv);
  BTOR_RUN_TEST (prop_complete_and_bv);
  BTOR_RUN_TEST (prop_complete_eq_bv);
  BTOR_RUN_TEST (prop_complete_ult_bv);
  BTOR_RUN_TEST (prop_complete_sll_bv);
  BTOR_RUN_TEST (prop_complete_srl_bv);
  BTOR_RUN_TEST (prop_complete_mul_bv);
  BTOR_RUN_TEST (prop_complete_udiv_bv);
  BTOR_RUN_TEST (prop_complete_urem_bv);
  BTOR_RUN_TEST (prop_complete_concat_bv);
  BTOR_RUN_TEST (prop_complete_slice_bv);
}

void
finish_prop_tests (void)
{
}

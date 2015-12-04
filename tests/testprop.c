/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testprop.h"
#include "btorbitvec.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btormodel.h"
#include "btorprop.h"
#include "btorsls.h"
#include "testrunner.h"
#include "utils/btorutil.h"

static Btor *g_btor;
static BtorMemMgr *g_mm;
static BtorRNG *g_rng;

#define TEST_PROP_ONE_COMPLETE_BW 4
#define TEST_PROP_ONE_COMPLETE_N_TESTS 1000

#define TEST_PROP_ONE_COMPLETE_BINARY_INIT(fun)                        \
  do                                                                   \
  {                                                                    \
    g_btor                            = btor_new_btor ();              \
    g_btor->slv                       = btor_new_prop_solver (g_btor); \
    g_btor->options.engine.val        = BTOR_ENGINE_PROP;              \
    g_btor->options.rewrite_level.val = 0;                             \
    g_btor->options.sort_exp.val      = 0;                             \
    g_btor->options.incremental.val   = 1;                             \
    g_btor->options.loglevel.val      = 1;                             \
    g_mm                              = g_btor->mm;                    \
    g_rng                             = &g_btor->rng;                  \
    bw                                = TEST_PROP_ONE_COMPLETE_BW;     \
  } while (0)

#define TEST_PROP_ONE_COMPLETE_BINARY_FINISH(fun) \
  do                                              \
  {                                               \
    btor_delete_btor (g_btor);                    \
  } while (0)

static inline void
prop_one_complete_binary_eidx (
    int eidx,
    uint32_t bw,
    BtorBitVector *bve,
    BtorBitVector *bvres,
    BtorBitVector *bvexp,
    BtorNode *(*create_exp) (Btor *, BtorNode *, BtorNode *),
    BtorBitVector *(*create_bv) (BtorMemMgr *,
                                 BtorBitVector *,
                                 BtorBitVector *),
    BtorBitVector *(*inv_bv) (
        Btor *, BtorNode *, BtorBitVector *, BtorBitVector *, int) )
{
  int i, sat_res;
  BtorNode *e[2], *exp, *val, *eq;
  BtorBitVector *bvetmp, *bvexptmp, *res, *tmp;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  exp  = create_exp (g_btor, e[0], e[1]);
  val  = btor_const_exp (g_btor, bvexp);
  eq   = btor_eq_exp (g_btor, exp, val);

  bvetmp = btor_new_random_bv (g_mm, g_rng, bw);
  // bvetmp = btor_char_to_bv (g_mm, "1100");
  bvexptmp =
      eidx ? create_bv (g_mm, bve, bvetmp) : create_bv (g_mm, bvetmp, bve);
  /* init bv model */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_init_fun_model (g_btor, &g_btor->fun_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[eidx ? 0 : 1], bve);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[eidx], bvetmp);

  /* -> first test local completeness  */
  /* we must find a solution within one move */
  res = inv_bv (g_btor, exp, bvexp, bve, eidx);
  assert (res);
  /* Note: this is also tested within the inverse function(s) */
  tmp = eidx ? create_bv (g_mm, bve, res) : create_bv (g_mm, res, bve);
  assert (!btor_compare_bv (tmp, bvexp));
  btor_free_bv (g_mm, tmp);
  btor_free_bv (g_mm, res);
  /* try to find the exact given solution */
  for (i = 0, res = 0; i < TEST_PROP_ONE_COMPLETE_N_TESTS; i++)
  {
    res = inv_bv (g_btor, exp, bvexp, bve, eidx);
    assert (res);
    if (!btor_compare_bv (res, bvres)) break;
    btor_free_bv (g_mm, res);
    res = 0;
  }
  assert (res);
  assert (!btor_compare_bv (res, bvres));
  btor_free_bv (g_mm, res);

  /* -> then test completeness of the whole propagation algorithm
   *    (we must find a solution within one move) */
  ((BtorPropSolver *) g_btor->slv)->stats.moves = 0;
  btor_assume_exp (g_btor, eq);
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_init_fun_model (g_btor, &g_btor->fun_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[eidx ? 0 : 1], bve);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[eidx], bvetmp);
  //  printf ("eidx %d bve %s bvetmp %s bvexp %s bvexptmp %s\n", eidx,
  //  btor_bv_to_char_bv (g_mm, bve), btor_bv_to_char_bv (g_mm, bvetmp),
  //  btor_bv_to_char_bv (g_mm, bvexp), btor_bv_to_char_bv (g_mm, bvexptmp));
  //  printf ("e[0] %s e[1] %s exp %s\n", btor_bv_to_char_bv (g_mm,
  //  btor_get_bv_model (g_btor, e[0])), btor_bv_to_char_bv (g_mm,
  //  btor_get_bv_model (g_btor, e[1])), btor_bv_to_char_bv (g_mm,
  //  btor_get_bv_model (g_btor, exp)));
  btor_free_bv (g_mm, bvetmp);
  btor_free_bv (g_mm, bvexptmp);
  btor_release_exp (g_btor, eq);
  btor_release_exp (g_btor, val);
  btor_release_exp (g_btor, exp);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
  sat_res = sat_prop_solver_aux (g_btor, -1, -1);
  assert (sat_res == BTOR_SAT);
  assert (((BtorPropSolver *) g_btor->slv)->stats.moves <= 1);
}

static void
prop_one_complete_binary (
    BtorNode *(*create_exp) (Btor *, BtorNode *, BtorNode *),
    BtorBitVector *(*create_bv) (BtorMemMgr *,
                                 BtorBitVector *,
                                 BtorBitVector *),
    BtorBitVector *(*inv_bv) (
        Btor *, BtorNode *, BtorBitVector *, BtorBitVector *, int) )
{
  uint32_t bw;
  uint64_t i, j, k;
  BtorBitVector *bve[2], *bvexp;

  TEST_PROP_ONE_COMPLETE_BINARY_INIT (create_exp);

  for (i = 0; i < (uint32_t) (1 << bw); i++)
  {
    bve[0] = btor_uint64_to_bv (g_mm, i, bw);
    for (j = 0; j < (uint32_t) (1 << bw); j++)
    {
      bve[1] = btor_uint64_to_bv (g_mm, j, bw);
      bvexp  = create_bv (g_mm, bve[0], bve[1]);
      // printf (">>> bve[0] %s bve[1] %s bvexp %s \n", btor_bv_to_char_bv
      // (g_mm, bve[0]), btor_bv_to_char_bv (g_mm, bve[1]), btor_bv_to_char_bv
      // (g_mm, bvexp));
      for (k = 0; k < bw; k++)
      {
        prop_one_complete_binary_eidx (
            1, bw, bve[0], bve[1], bvexp, create_exp, create_bv, inv_bv);
        prop_one_complete_binary_eidx (
            0, bw, bve[1], bve[0], bvexp, create_exp, create_bv, inv_bv);
      }
      btor_free_bv (g_mm, bve[1]);
      btor_free_bv (g_mm, bvexp);
    }
    btor_free_bv (g_mm, bve[0]);
  }

  TEST_PROP_ONE_COMPLETE_BINARY_FINISH (fun);
}
#if 0

#define TEST_PROP_ONE_COMPLETE_SHIFT_INIT(fun)    \
  do                                              \
  {                                               \
    bw   = TEST_PROP_ONE_COMPLETE_BW;             \
    sbw  = btor_log_2_util (bw);                  \
    e[0] = btor_var_exp (g_btor, bw, 0);          \
    e[1] = btor_var_exp (g_btor, sbw, 0);         \
    exp  = btor_##fun##_exp (g_btor, e[0], e[1]); \
  } while (0)

#define TEST_PROP_ONE_COMPLETE_SHIFT(fun)                            \
  do                                                                 \
  {                                                                  \
    uint32_t bw, sbw;                                                \
    uint64_t i, j, k;                                                \
    BtorNode *exp, *e[2];                                            \
    BtorBitVector *bve[2], *bvexp, *res;                             \
    TEST_PROP_ONE_COMPLETE_SHIFT_INIT (fun);                         \
    for (i = 0; i < (uint32_t) (1 << bw); i++)                       \
    {                                                                \
      bve[0] = btor_uint64_to_bv (g_mm, i, bw);                      \
      for (j = 0; j < (uint32_t) (1 << sbw); j++)                    \
      {                                                              \
        bve[1] = btor_uint64_to_bv (g_mm, j, sbw);                   \
        bvexp  = btor_##fun##_bv (g_mm, bve[0], bve[1]);             \
        TEST_PROP_ONE_COMPLETE_EIDX (fun, bve[0], bvexp, bve[1], 1); \
        TEST_PROP_ONE_COMPLETE_EIDX (fun, bve[1], bvexp, bve[0], 0); \
        btor_free_bv (g_mm, bve[1]);                                 \
        btor_free_bv (g_mm, bvexp);                                  \
      }                                                              \
      btor_free_bv (g_mm, bve[0]);                                   \
    }                                                                \
    TEST_PROP_ONE_COMPLETE_BINARY_FINISH (fun);                      \
  } while (0)
#endif

static void
test_prop_one_complete_add_bv (void)
{
#ifndef NDEBUG
  prop_one_complete_binary (btor_add_exp, btor_add_bv, inv_add_bv);
#endif
}

static void
test_prop_one_complete_and_bv (void)
{
#ifndef NDEBUG
  prop_one_complete_binary (btor_and_exp, btor_and_bv, inv_and_bv);
#endif
}

static void
test_prop_one_complete_eq_bv (void)
{
#ifndef NDEBUG
  prop_one_complete_binary (btor_eq_exp, btor_eq_bv, inv_eq_bv);
#endif
}

static void
test_prop_one_complete_ult_bv (void)
{
#ifndef NDEBUG
  prop_one_complete_binary (btor_ult_exp, btor_ult_bv, inv_ult_bv);
#endif
}

#if 0
static void
test_prop_one_complete_sll_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_ONE_COMPLETE_SHIFT (sll);
#endif
}

static void
test_prop_one_complete_srl_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_ONE_COMPLETE_SHIFT (srl);
#endif
}
#endif

static void
test_prop_one_complete_mul_bv (void)
{
#ifndef NDEBUG
  prop_one_complete_binary (btor_mul_exp, btor_mul_bv, inv_mul_bv);
#endif
}

static void
test_prop_one_complete_udiv_bv (void)
{
#ifndef NDEBUG
  prop_one_complete_binary (btor_udiv_exp, btor_udiv_bv, inv_udiv_bv);
#endif
}

static void
test_prop_one_complete_urem_bv (void)
{
#ifndef NDEBUG
  prop_one_complete_binary (btor_urem_exp, btor_urem_bv, inv_urem_bv);
#endif
}

#if 0
static void
test_prop_one_complete_concat_bv (void)
{
#ifndef NDEBUG
  TEST_PROP_ONE_COMPLETE_BINARY (concat);
#endif
}

static void
test_prop_one_complete_slice_bv (void)
{
#ifndef NDEBUG
  uint32_t bw;
  uint64_t up, lo, i, k;
  BtorNode *exp, *e;
  BtorBitVector *bve, *bvexp, *res;

  bw = TEST_PROP_ONE_COMPLETE_BW;
  e = btor_var_exp (g_btor, bw, 0);

  for (lo = 0; lo < bw; lo++)
    {
      for (up = lo; up < bw; up++)
	{
	  exp = btor_slice_exp (g_btor, e, up, lo);
	  for (i = 0; i < (uint32_t) (1 << bw); i++)
	    {
	      bve = btor_uint64_to_bv (g_mm, i, bw);
	      bvexp = btor_slice_bv (g_mm, bve, up, lo);
	      for (k = 0, res = 0; k < TEST_PROP_ONE_COMPLETE_N_TESTS; k++)
		{
		  res = inv_slice_bv (g_btor, exp, bvexp);
		  assert (res);
		  if (!btor_compare_bv (res, bve)) break;
		  btor_free_bv (g_mm, res);
		  res = 0;
		}
	      assert (res);
	      assert (!btor_compare_bv (res, bve));
	      btor_free_bv (g_mm, res);
	      btor_free_bv (g_mm, bvexp);
	      btor_free_bv (g_mm, bve);
	    }
	  btor_release_exp (g_btor, exp);
	}
    }
  btor_release_exp (g_btor, e);
#endif
}
#endif

/*------------------------------------------------------------------------*/

void
init_prop_tests (void)
{
}

void
run_prop_tests (int argc, char **argv)
{
  (void) argc;
  (void) argv;
  BTOR_RUN_TEST (prop_one_complete_add_bv);
  BTOR_RUN_TEST (prop_one_complete_and_bv);
  BTOR_RUN_TEST (prop_one_complete_eq_bv);
  BTOR_RUN_TEST (prop_one_complete_ult_bv);
  //  BTOR_RUN_TEST (prop_one_complete_sll_bv);
  //  BTOR_RUN_TEST (prop_one_complete_srl_bv);
  BTOR_RUN_TEST (prop_one_complete_mul_bv);
  BTOR_RUN_TEST (prop_one_complete_udiv_bv);
  BTOR_RUN_TEST (prop_one_complete_urem_bv);
  //  BTOR_RUN_TEST (prop_one_complete_concat_bv);
  //  BTOR_RUN_TEST (prop_one_complete_slice_bv);
}

void
finish_prop_tests (void)
{
}

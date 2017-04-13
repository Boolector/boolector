/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2014-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testaigvec.h"
#include "btoraigvec.h"
#include "btorbitvec.h"
#include "btorcore.h"
#include "testrunner.h"
#include "utils/btormem.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdint.h>

static Btor *g_btor;

void
init_aigvec_tests (void)
{
  g_btor = btor_new_btor ();
}

static void
test_new_delete_aigvec_mgr (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_const_aigvec (void)
{
  BtorBitVector *bits  = btor_uint64_to_bv (g_btor->mm, 11, 4);  // "1011"
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av       = btor_aigvec_const (avmgr, bits);
  assert (av->len == 4);
  btor_aigvec_release_delete (avmgr, av);
  btor_aigvec_delete_mgr (avmgr);
  btor_free_bv (g_btor->mm, bits);
}

static void
test_var_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av       = btor_aigvec_var (avmgr, 32);
  assert (av->len == 32);
  btor_aigvec_release_delete (avmgr, av);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_invert_aigvec (void)
{
  int i                = 0;
  int len              = 0;
  BtorBitVector *bits  = btor_uint64_to_bv (g_btor->mm, 11, 4);  // "1011"
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_const (avmgr, bits);
  len                  = av1->len;
  assert (len == 32);
  for (i = 0; i < len; i++)
  {
    assert (!BTOR_IS_INVERTED_AIG (av1->aigs[i]));
    assert (btor_aig_is_var (av1->aigs[i]));
  }
  btor_aigvec_invert (avmgr, av1);
  for (i = 0; i < len; i++) assert (BTOR_IS_INVERTED_AIG (av1->aigs[i]));
  btor_aigvec_invert (avmgr, av1);
  for (i = 0; i < len; i++)
  {
    assert (!BTOR_IS_INVERTED_AIG (av1->aigs[i]));
    assert (btor_aig_is_var (av1->aigs[i]));
  }
  assert (av2->aigs[0] == BTOR_AIG_TRUE);
  assert (av2->aigs[1] == BTOR_AIG_FALSE);
  assert (av2->aigs[2] == BTOR_AIG_TRUE);
  assert (av2->aigs[3] == BTOR_AIG_TRUE);
  btor_aigvec_invert (avmgr, av2);
  assert (av2->aigs[0] == BTOR_AIG_FALSE);
  assert (av2->aigs[1] == BTOR_AIG_TRUE);
  assert (av2->aigs[2] == BTOR_AIG_FALSE);
  assert (av2->aigs[3] == BTOR_AIG_FALSE);
  btor_aigvec_invert (avmgr, av2);
  assert (av2->aigs[0] == BTOR_AIG_TRUE);
  assert (av2->aigs[1] == BTOR_AIG_FALSE);
  assert (av2->aigs[2] == BTOR_AIG_TRUE);
  assert (av2->aigs[3] == BTOR_AIG_TRUE);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_delete_mgr (avmgr);
  btor_free_bv (g_btor->mm, bits);
}

static void
test_not_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_not (avmgr, av1);
  assert (av2->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_slice_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_slice (avmgr, av1, 17, 2);
  assert (av2->len == 16);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_and_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_and (avmgr, av1, av2);
  assert (av3->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_ult_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_ult (avmgr, av1, av2);
  assert (av3->len == 1);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_eq_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_eq (avmgr, av1, av2);
  assert (av3->len == 1);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_add_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_add (avmgr, av1, av2);
  assert (av3->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_sll_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 5);
  BtorAIGVec *av3      = btor_aigvec_sll (avmgr, av1, av2);
  assert (av3->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_srl_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 5);
  BtorAIGVec *av3      = btor_aigvec_srl (avmgr, av1, av2);
  assert (av3->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_mul_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_mul (avmgr, av1, av2);
  assert (av3->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_udiv_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_udiv (avmgr, av1, av2);
  assert (av3->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_urem_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_urem (avmgr, av1, av2);
  assert (av3->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_concat_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 16);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_concat (avmgr, av1, av2);
  assert (av3->len == 48);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_delete_mgr (avmgr);
}

static void
test_cond_aigvec (void)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_new_mgr (g_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 1);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av4      = btor_aigvec_cond (avmgr, av1, av2, av3);
  assert (av4->len == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_release_delete (avmgr, av4);
  btor_aigvec_delete_mgr (avmgr);
}

void
run_aigvec_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_aigvec_mgr);
  BTOR_RUN_TEST (const_aigvec);
  BTOR_RUN_TEST (var_aigvec);
  BTOR_RUN_TEST (invert_aigvec);
  BTOR_RUN_TEST (not_aigvec);
  BTOR_RUN_TEST (slice_aigvec);
  BTOR_RUN_TEST (and_aigvec);
  BTOR_RUN_TEST (ult_aigvec);
  BTOR_RUN_TEST (eq_aigvec);
  BTOR_RUN_TEST (add_aigvec);
  BTOR_RUN_TEST (sll_aigvec);
  BTOR_RUN_TEST (srl_aigvec);
  BTOR_RUN_TEST (mul_aigvec);
  BTOR_RUN_TEST (udiv_aigvec);
  BTOR_RUN_TEST (urem_aigvec);
  BTOR_RUN_TEST (concat_aigvec);
  BTOR_RUN_TEST (cond_aigvec);
}

void
finish_aigvec_tests (void)
{
  btor_delete_btor (g_btor);
}

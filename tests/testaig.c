/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testaig.h"
#include "btoraig.h"
#include "btorcore.h"
#include "btormsg.h"
#include "btorsat.h"
#include "dumper/btordumpaig.h"
#include "testrunner.h"
#include "utils/btormem.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static Btor *g_btor;

void
init_aig_tests (void)
{
  g_btor = btor_new_btor ();
}

static void
test_new_delete_aig_mgr (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_btor);
  btor_delete_aig_mgr (amgr);
}

static void
test_false_aig (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_btor);
  btor_dump_aig (amgr, 0, g_logfile, BTOR_AIG_FALSE);
  btor_delete_aig_mgr (amgr);
}

static void
test_true_aig (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_btor);
  btor_dump_aig (amgr, 0, g_logfile, BTOR_AIG_TRUE);
  btor_delete_aig_mgr (amgr);
}

static void
test_var_aig (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_btor);
  BtorAIG *var     = btor_var_aig (amgr);
  assert (BTOR_IS_VAR_AIG (var));
  btor_dump_aig (amgr, 0, g_logfile, var);
  btor_release_aig (amgr, var);
  btor_delete_aig_mgr (amgr);
}

static void
test_not_aig (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_btor);
  BtorAIG *var     = btor_var_aig (amgr);
  BtorAIG *not     = btor_not_aig (amgr, var);
  btor_dump_aig (amgr, 0, g_logfile, not);
  btor_release_aig (amgr, var);
  btor_release_aig (amgr, not);
  btor_delete_aig_mgr (amgr);
}

static void
binary_commutative_aig_test (BtorAIG *(*func) (BtorAIGMgr *,
                                               BtorAIG *,
                                               BtorAIG *) )
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_btor);
  BtorAIG *aig1    = btor_var_aig (amgr);
  BtorAIG *aig2    = btor_var_aig (amgr);
  BtorAIG *aig3    = func (amgr, aig1, aig2);
  BtorAIG *aig4    = func (amgr, aig1, aig2);
  BtorAIG *aig5    = func (amgr, aig2, aig1);
  assert (aig3 == aig4);
  assert (aig4 == aig5);
  btor_dump_aig (amgr, 0, g_logfile, aig5);
  btor_release_aig (amgr, aig1);
  btor_release_aig (amgr, aig2);
  btor_release_aig (amgr, aig3);
  btor_release_aig (amgr, aig4);
  btor_release_aig (amgr, aig5);
  btor_delete_aig_mgr (amgr);
}

static void
test_and_aig (void)
{
  binary_commutative_aig_test (btor_and_aig);
}

static void
test_or_aig (void)
{
  binary_commutative_aig_test (btor_or_aig);
}

static void
test_eq_aig (void)
{
  binary_commutative_aig_test (btor_eq_aig);
}

static void
test_cond_aig (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_btor);
  BtorAIG *aig1    = btor_var_aig (amgr);
  BtorAIG *aig2    = btor_var_aig (amgr);
  BtorAIG *aig3    = btor_var_aig (amgr);
  BtorAIG *aig4    = btor_cond_aig (amgr, aig1, aig2, aig3);
  BtorAIG *aig5    = btor_cond_aig (amgr, aig1, aig2, aig3);
  assert (aig4 == aig5);
  btor_dump_aig (amgr, 0, g_logfile, aig5);
  btor_release_aig (amgr, aig1);
  btor_release_aig (amgr, aig2);
  btor_release_aig (amgr, aig3);
  btor_release_aig (amgr, aig4);
  btor_release_aig (amgr, aig5);
  btor_delete_aig_mgr (amgr);
}

static void
test_aig_to_sat (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_btor);
  BtorSATMgr *smgr = btor_get_sat_mgr_aig_mgr (amgr);
  BtorAIG *var1    = btor_var_aig (amgr);
  BtorAIG *var2    = btor_var_aig (amgr);
  BtorAIG *var3    = btor_var_aig (amgr);
  BtorAIG *var4    = btor_var_aig (amgr);
  BtorAIG *and1    = btor_and_aig (amgr, var1, var2);
  BtorAIG *and2    = btor_and_aig (amgr, var3, var4);
  BtorAIG *and3    = btor_or_aig (amgr, and1, and2);
  btor_init_sat (smgr);
  btor_aig_to_sat (amgr, and3);
  btor_reset_sat (smgr);
  btor_release_aig (amgr, var1);
  btor_release_aig (amgr, var2);
  btor_release_aig (amgr, var3);
  btor_release_aig (amgr, var4);
  btor_release_aig (amgr, and1);
  btor_release_aig (amgr, and2);
  btor_release_aig (amgr, and3);
  btor_delete_aig_mgr (amgr);
}

void
run_aig_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_aig_mgr);
  BTOR_RUN_TEST_CHECK_LOG (false_aig);
  BTOR_RUN_TEST_CHECK_LOG (true_aig);
  BTOR_RUN_TEST_CHECK_LOG (var_aig);
  BTOR_RUN_TEST_CHECK_LOG (not_aig);
  BTOR_RUN_TEST_CHECK_LOG (and_aig);
  BTOR_RUN_TEST_CHECK_LOG (or_aig);
  BTOR_RUN_TEST_CHECK_LOG (eq_aig);
  BTOR_RUN_TEST_CHECK_LOG (cond_aig);
  BTOR_RUN_TEST (aig_to_sat);
}

void
finish_aig_tests (void)
{
  btor_delete_btor (g_btor);
}

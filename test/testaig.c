/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014-2017 Aina Niemetz.
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
  g_btor = btor_new ();
}

static void
test_new_delete_aig_mgr (void)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (g_btor);
  btor_aig_mgr_delete (amgr);
}

static void
test_false_aig (void)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (g_btor);
  btor_dumpaig_dump_aig (amgr, 0, g_logfile, BTOR_AIG_FALSE);
  btor_aig_mgr_delete (amgr);
}

static void
test_true_aig (void)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (g_btor);
  btor_dumpaig_dump_aig (amgr, 0, g_logfile, BTOR_AIG_TRUE);
  btor_aig_mgr_delete (amgr);
}

static void
test_var_aig (void)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (g_btor);
  BtorAIG *var     = btor_aig_var (amgr);
  assert (btor_aig_is_var (var));
  btor_dumpaig_dump_aig (amgr, 0, g_logfile, var);
  btor_aig_release (amgr, var);
  btor_aig_mgr_delete (amgr);
}

static void
test_not_aig (void)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (g_btor);
  BtorAIG *var     = btor_aig_var (amgr);
  BtorAIG *not     = btor_aig_not (amgr, var);
  btor_dumpaig_dump_aig (amgr, 0, g_logfile, not);
  btor_aig_release (amgr, var);
  btor_aig_release (amgr, not);
  btor_aig_mgr_delete (amgr);
}

static void
binary_commutative_aig_test (BtorAIG *(*func) (BtorAIGMgr *,
                                               BtorAIG *,
                                               BtorAIG *) )
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (g_btor);
  BtorAIG *aig1    = btor_aig_var (amgr);
  BtorAIG *aig2    = btor_aig_var (amgr);
  BtorAIG *aig3    = func (amgr, aig1, aig2);
  BtorAIG *aig4    = func (amgr, aig1, aig2);
  BtorAIG *aig5    = func (amgr, aig2, aig1);
  assert (aig3 == aig4);
  assert (aig4 == aig5);
  btor_dumpaig_dump_aig (amgr, 0, g_logfile, aig5);
  btor_aig_release (amgr, aig1);
  btor_aig_release (amgr, aig2);
  btor_aig_release (amgr, aig3);
  btor_aig_release (amgr, aig4);
  btor_aig_release (amgr, aig5);
  btor_aig_mgr_delete (amgr);
}

static void
test_and_aig (void)
{
  binary_commutative_aig_test (btor_aig_and);
}

static void
test_or_aig (void)
{
  binary_commutative_aig_test (btor_aig_or);
}

static void
test_eq_aig (void)
{
  binary_commutative_aig_test (btor_aig_eq);
}

static void
test_cond_aig (void)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (g_btor);
  BtorAIG *aig1    = btor_aig_var (amgr);
  BtorAIG *aig2    = btor_aig_var (amgr);
  BtorAIG *aig3    = btor_aig_var (amgr);
  BtorAIG *aig4    = btor_aig_cond (amgr, aig1, aig2, aig3);
  BtorAIG *aig5    = btor_aig_cond (amgr, aig1, aig2, aig3);
  assert (aig4 == aig5);
  btor_dumpaig_dump_aig (amgr, 0, g_logfile, aig5);
  btor_aig_release (amgr, aig1);
  btor_aig_release (amgr, aig2);
  btor_aig_release (amgr, aig3);
  btor_aig_release (amgr, aig4);
  btor_aig_release (amgr, aig5);
  btor_aig_mgr_delete (amgr);
}

static void
test_aig_to_sat (void)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (g_btor);
  BtorSATMgr *smgr = btor_aig_get_sat_mgr (amgr);
  BtorAIG *var1    = btor_aig_var (amgr);
  BtorAIG *var2    = btor_aig_var (amgr);
  BtorAIG *var3    = btor_aig_var (amgr);
  BtorAIG *var4    = btor_aig_var (amgr);
  BtorAIG *and1    = btor_aig_and (amgr, var1, var2);
  BtorAIG *and2    = btor_aig_and (amgr, var3, var4);
  BtorAIG *and3    = btor_aig_or (amgr, and1, and2);
  btor_sat_enable_solver (smgr);
  btor_sat_init (smgr);
  btor_aig_to_sat (amgr, and3);
  btor_sat_reset (smgr);
  btor_aig_release (amgr, var1);
  btor_aig_release (amgr, var2);
  btor_aig_release (amgr, var3);
  btor_aig_release (amgr, var4);
  btor_aig_release (amgr, and1);
  btor_aig_release (amgr, and2);
  btor_aig_release (amgr, and3);
  btor_aig_mgr_delete (amgr);
}

void
run_aig_tests (int32_t argc, char **argv)
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
  btor_delete (g_btor);
}

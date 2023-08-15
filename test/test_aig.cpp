/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#include "test.h"

extern "C" {
#include "btoraig.h"
#include "dumper/btordumpaig.h"
}

class TestAig : public TestBtor
{
 protected:
  void binary_commutative_aig_test (BtorAIG *(*func) (BtorAIGMgr *,
                                                      BtorAIG *,
                                                      BtorAIG *) )
  {
    BtorAIGMgr *amgr = btor_aig_mgr_new (d_btor);
    BtorAIG *aig1    = btor_aig_var (amgr);
    BtorAIG *aig2    = btor_aig_var (amgr);
    BtorAIG *aig3    = func (amgr, aig1, aig2);
    BtorAIG *aig4    = func (amgr, aig1, aig2);
    BtorAIG *aig5    = func (amgr, aig2, aig1);
    ASSERT_TRUE (aig3 == aig4);
    ASSERT_TRUE (aig4 == aig5);
    btor_dumpaig_dump_aig (amgr, 0, d_log_file, aig5);
    btor_aig_release (amgr, aig1);
    btor_aig_release (amgr, aig2);
    btor_aig_release (amgr, aig3);
    btor_aig_release (amgr, aig4);
    btor_aig_release (amgr, aig5);
    btor_aig_mgr_delete (amgr);
  }
};

TEST_F (TestAig, new_delete_aig_mgr)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (d_btor);
  btor_aig_mgr_delete (amgr);
}

TEST_F (TestAig, false)
{
  open_log_file ("false_aig");
  BtorAIGMgr *amgr = btor_aig_mgr_new (d_btor);
  btor_dumpaig_dump_aig (amgr, 0, d_log_file, BTOR_AIG_FALSE);
  btor_aig_mgr_delete (amgr);
}

TEST_F (TestAig, true)
{
  open_log_file ("true_aig");
  BtorAIGMgr *amgr = btor_aig_mgr_new (d_btor);
  btor_dumpaig_dump_aig (amgr, 0, d_log_file, BTOR_AIG_TRUE);
  btor_aig_mgr_delete (amgr);
}

TEST_F (TestAig, var)
{
  open_log_file ("var_aig");
  BtorAIGMgr *amgr = btor_aig_mgr_new (d_btor);
  BtorAIG *var     = btor_aig_var (amgr);
  ASSERT_TRUE (btor_aig_is_var (var));
  btor_dumpaig_dump_aig (amgr, 0, d_log_file, var);
  btor_aig_release (amgr, var);
  btor_aig_mgr_delete (amgr);
}

TEST_F (TestAig, not)
{
  open_log_file ("not_aig");
  BtorAIGMgr *amgr = btor_aig_mgr_new (d_btor);
  BtorAIG *var     = btor_aig_var (amgr);
  BtorAIG *_not    = btor_aig_not (amgr, var);
  btor_dumpaig_dump_aig (amgr, 0, d_log_file, _not);
  btor_aig_release (amgr, var);
  btor_aig_release (amgr, _not);
  btor_aig_mgr_delete (amgr);
}

TEST_F (TestAig, and)
{
  open_log_file ("and_aig");
  binary_commutative_aig_test (btor_aig_and);
}

TEST_F (TestAig, or)
{
  open_log_file ("or_aig");
  binary_commutative_aig_test (btor_aig_or);
}

TEST_F (TestAig, eq)
{
  open_log_file ("eq_aig");
  binary_commutative_aig_test (btor_aig_eq);
}

TEST_F (TestAig, cond)
{
  open_log_file ("cond_aig");
  BtorAIGMgr *amgr = btor_aig_mgr_new (d_btor);
  BtorAIG *aig1    = btor_aig_var (amgr);
  BtorAIG *aig2    = btor_aig_var (amgr);
  BtorAIG *aig3    = btor_aig_var (amgr);
  BtorAIG *aig4    = btor_aig_cond (amgr, aig1, aig2, aig3);
  BtorAIG *aig5    = btor_aig_cond (amgr, aig1, aig2, aig3);
  ASSERT_TRUE (aig4 == aig5);
  btor_dumpaig_dump_aig (amgr, 0, d_log_file, aig5);
  btor_aig_release (amgr, aig1);
  btor_aig_release (amgr, aig2);
  btor_aig_release (amgr, aig3);
  btor_aig_release (amgr, aig4);
  btor_aig_release (amgr, aig5);
  btor_aig_mgr_delete (amgr);
}

TEST_F (TestAig, aig_to_sat)
{
  BtorAIGMgr *amgr = btor_aig_mgr_new (d_btor);
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

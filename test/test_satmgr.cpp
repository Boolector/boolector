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

class TestSatMgr : public TestBtor
{
 protected:
  void SetUp () override
  {
    TestBtor::SetUp ();
    d_smgr = btor_sat_mgr_new (d_btor);
  }
  void TearDown () override
  {
    btor_sat_mgr_delete (d_smgr);
    TestBtor::TearDown ();
  }
  BtorSATMgr *d_smgr = nullptr;
};

TEST_F (TestSatMgr, new_delete) {}

TEST_F (TestSatMgr, next_cnf_id)
{
  btor_sat_enable_solver (d_smgr);
  btor_sat_init (d_smgr);
  ASSERT_EQ (btor_sat_mgr_next_cnf_id (d_smgr), 2);
  ASSERT_EQ (btor_sat_mgr_next_cnf_id (d_smgr), 3);
  ASSERT_EQ (btor_sat_mgr_next_cnf_id (d_smgr), 4);
  btor_sat_reset (d_smgr);
}

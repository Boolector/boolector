/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2016-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolector.h"
#include "btorconfig.h"
}

class TestModelGen : public TestFile
{
 protected:
  void SetUp () override
  {
    TestFile::SetUp ();
    d_check_log_file = false;
  }

  void run_modelgen_test (const char* name, const char* ext, int32_t rwl)
  {
#ifndef BTOR_WINDOWS_BUILD
    int32_t ret_val;
#endif
    assert (rwl >= 0);
    assert (rwl <= 3);

    boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, rwl);
    boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
    d_get_model = true;

    run_test (name, ext, BOOLECTOR_UNKNOWN);
    fclose (d_log_file);
    d_log_file = nullptr;

#ifndef BTOR_WINDOWS_BUILD
    std::stringstream ss_cmd;
    ss_cmd << BTOR_CONTRIB_DIR << "btorcheckmodel.py " << BTOR_OUT_DIR << name
           << ext << " " << d_log_file_name << " " << BTOR_BIN_DIR
           << "boolector > /dev/null";
    ret_val = system (ss_cmd.str ().c_str ());
    ASSERT_EQ (ret_val, 0);
#endif
  }
};

TEST_F (TestModelGen, modelgen1)
{
  run_modelgen_test ("modelgen1", ".btor", 1);
}

TEST_F (TestModelGen, modelgen2)
{
  run_modelgen_test ("modelgen2", ".btor", 3);
}

TEST_F (TestModelGen, modelgen3)
{
  run_modelgen_test ("modelgen3", ".btor", 3);
}

TEST_F (TestModelGen, modelgen4)
{
  run_modelgen_test ("modelgen4", ".btor", 3);
}

TEST_F (TestModelGen, modelgen5)
{
  run_modelgen_test ("modelgen5", ".btor", 3);
}

TEST_F (TestModelGen, modelgen6)
{
  run_modelgen_test ("modelgen6", ".btor", 3);
}

TEST_F (TestModelGen, modelgen7)
{
  run_modelgen_test ("modelgen7", ".btor", 3);
}

TEST_F (TestModelGen, modelgen8)
{
  run_modelgen_test ("modelgen8", ".btor", 0);
}

TEST_F (TestModelGen, modelgen9)
{
  run_modelgen_test ("modelgen9", ".btor", 3);
}

TEST_F (TestModelGen, modelgen10)
{
  run_modelgen_test ("modelgen10", ".btor", 3);
}

TEST_F (TestModelGen, modelgen11)
{
  run_modelgen_test ("modelgen11", ".btor", 3);
}

TEST_F (TestModelGen, modelgen12)
{
  run_modelgen_test ("modelgen12", ".btor", 3);
}

TEST_F (TestModelGen, modelgen13)
{
  run_modelgen_test ("modelgen13", ".btor", 3);
}

TEST_F (TestModelGen, modelgen14)
{
  run_modelgen_test ("modelgen14", ".btor", 3);
}

TEST_F (TestModelGen, modelgen15)
{
  run_modelgen_test ("modelgen15", ".btor", 3);
}

TEST_F (TestModelGen, modelgen16)
{
  run_modelgen_test ("modelgen16", ".btor", 1);
}

TEST_F (TestModelGen, modelgen17)
{
  run_modelgen_test ("modelgen17", ".btor", 1);
}

TEST_F (TestModelGen, modelgen18)
{
  run_modelgen_test ("modelgen18", ".btor", 3);
}

TEST_F (TestModelGen, modelgen19)
{
  run_modelgen_test ("modelgen19", ".btor", 2);
}

TEST_F (TestModelGen, modelgen20)
{
  run_modelgen_test ("modelgen20", ".btor", 3);
}

TEST_F (TestModelGen, modelgen21)
{
  run_modelgen_test ("modelgen21", ".btor", 3);
}

TEST_F (TestModelGen, modelgen22)
{
  run_modelgen_test ("modelgen22", ".btor", 3);
}

TEST_F (TestModelGen, modelgen23)
{
  run_modelgen_test ("modelgen23", ".btor", 3);
}

TEST_F (TestModelGen, modelgen24)
{
  run_modelgen_test ("modelgen24", ".btor", 3);
}

TEST_F (TestModelGen, modelgen25)
{
  run_modelgen_test ("modelgen25", ".btor", 3);
}

TEST_F (TestModelGen, modelgen26)
{
  run_modelgen_test ("modelgen26", ".btor", 3);
}

TEST_F (TestModelGen, modelgen27)
{
  run_modelgen_test ("modelgen27", ".btor", 3);
}

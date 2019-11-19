/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolector.h"
#include "btorconfig.h"
}

class TestModelGenSMT2 : public TestFile
{
 protected:
  void SetUp () override
  {
    TestFile::SetUp ();
    d_check_log_file = false;
  }

  void run_modelgen_smt2_test (const char* name, const char* ext, int32_t rwl)
  {
#ifndef BTOR_WINDOWS_BUILD
    int32_t ret_val;
#endif
    assert (rwl >= 0);
    assert (rwl <= 3);

    boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, rwl);
    boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
    d_get_model    = true;
    d_model_format = "smt2";

    run_test (name, ext, BOOLECTOR_UNKNOWN);
    fclose (d_log_file);
    d_log_file = nullptr;

#ifndef BTOR_WINDOWS_BUILD
    std::stringstream ss_cmd;
    ss_cmd << BTOR_CONTRIB_DIR << "btorcheckmodelsmt2.sh " << BTOR_OUT_DIR
           << name << ext << " " << d_log_file_name << " " << BTOR_BIN_DIR
           << "boolector > /dev/null";
    ret_val = system (ss_cmd.str ().c_str ());
    ASSERT_EQ (ret_val, 0);
#endif
  }
};

TEST_F (TestModelGenSMT2, modelgensmt21)
{
  run_modelgen_smt2_test ("modelgensmt21", ".smt2", 1);
}

TEST_F (TestModelGenSMT2, modelgensmt22)
{
  run_modelgen_smt2_test ("modelgensmt22", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt23)
{
  run_modelgen_smt2_test ("modelgensmt23", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt24)
{
  run_modelgen_smt2_test ("modelgensmt24", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt25)
{
  run_modelgen_smt2_test ("modelgensmt25", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt26)
{
  run_modelgen_smt2_test ("modelgensmt26", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt27)
{
  run_modelgen_smt2_test ("modelgensmt27", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt28)
{
  run_modelgen_smt2_test ("modelgensmt28", ".smt2", 0);
}

TEST_F (TestModelGenSMT2, modelgensmt29)
{
  run_modelgen_smt2_test ("modelgensmt29", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt210)
{
  run_modelgen_smt2_test ("modelgensmt210", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt211)
{
  run_modelgen_smt2_test ("modelgensmt211", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt212)
{
  run_modelgen_smt2_test ("modelgensmt212", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt213)
{
  run_modelgen_smt2_test ("modelgensmt213", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt214)
{
  run_modelgen_smt2_test ("modelgensmt214", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt215)
{
  run_modelgen_smt2_test ("modelgensmt215", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt216)
{
  run_modelgen_smt2_test ("modelgensmt216", ".smt2", 1);
}

TEST_F (TestModelGenSMT2, modelgensmt217)
{
  run_modelgen_smt2_test ("modelgensmt217", ".smt2", 1);
}

TEST_F (TestModelGenSMT2, modelgensmt218)
{
  run_modelgen_smt2_test ("modelgensmt218", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt219)
{
  run_modelgen_smt2_test ("modelgensmt219", ".smt2", 2);
}

TEST_F (TestModelGenSMT2, modelgensmt220)
{
  run_modelgen_smt2_test ("modelgensmt220", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt221)
{
  run_modelgen_smt2_test ("modelgensmt221", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt222)
{
  run_modelgen_smt2_test ("modelgensmt222", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt223)
{
  run_modelgen_smt2_test ("modelgensmt223", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt224)
{
  run_modelgen_smt2_test ("modelgensmt224", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt225)
{
  run_modelgen_smt2_test ("modelgensmt225", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt226)
{
  run_modelgen_smt2_test ("modelgensmt226", ".smt2", 3);
}

TEST_F (TestModelGenSMT2, modelgensmt227)
{
  run_modelgen_smt2_test ("modelgensmt227", ".smt2", 3);
}

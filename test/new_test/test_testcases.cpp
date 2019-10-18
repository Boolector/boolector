/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolector.h"
}

class TestTestCases : public TestFile
{
 protected:
  void run_test_case_test (const char* infile_name,
                           const char* ext,
                           const char* outfile_name)
  {
    if (d_out_file_name != outfile_name)
    {
      d_out_file_name = outfile_name;
    }
    run_test (infile_name, ext, BOOLECTOR_UNKNOWN);
  }
};

TEST_F (TestTestCases, smttrue)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  run_test_case_test ("smttrue", ".smt2", "smttrue");
}

TEST_F (TestTestCases, smtfalse)
{
  run_test_case_test ("smtfalse", ".smt2", "smtfalse");
}

TEST_F (TestTestCases, smtvar)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  run_test_case_test ("smtvar", ".smt2", "smtvar");
}

TEST_F (TestTestCases, smtnotvar)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  run_test_case_test ("smtnotvar", ".smt2", "smtnotvar");
}

TEST_F (TestTestCases, smtandvar)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  run_test_case_test ("smtandvar", ".smt2", "smtandvar");
}

TEST_F (TestTestCases, smtxor)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  run_test_case_test ("smtxor", ".smt2", "smtxor");
}

TEST_F (TestTestCases, smtor)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  run_test_case_test ("smtor", ".smt2", "smtor");
}

TEST_F (TestTestCases, smtiff)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  run_test_case_test ("smtiff", ".smt2", "smtiff");
}

TEST_F (TestTestCases, smtflet)
{
  run_test_case_test ("smtflet", ".smt2", "smtflet");
}

TEST_F (TestTestCases, smtbv255)
{
  run_test_case_test ("smtbv255", ".smt2", "smtbv255");
}

TEST_F (TestTestCases, smtshl1)
{
  run_test_case_test ("smtshl1", ".smt2", "smtshl1");
}

TEST_F (TestTestCases, smtshl2)
{
  run_test_case_test ("smtshl2", ".smt2", "smtshl2");
}

TEST_F (TestTestCases, smtshl3)
{
  run_test_case_test ("smtshl3", ".smt2", "smtshl3");
}

TEST_F (TestTestCases, smtlshr1)
{
  run_test_case_test ("smtlshr1", ".smt2", "smtlshr1");
}

TEST_F (TestTestCases, smtlshr2)
{
  run_test_case_test ("smtlshr2", ".smt2", "smtlshr2");
}

TEST_F (TestTestCases, smtlshr3)
{
  run_test_case_test ("smtlshr3", ".smt2", "smtlshr3");
}

TEST_F (TestTestCases, smtashr1)
{
  run_test_case_test ("smtashr1", ".smt2", "smtashr1");
}

TEST_F (TestTestCases, smtashr2)
{
  run_test_case_test ("smtashr2", ".smt2", "smtashr2");
}

TEST_F (TestTestCases, smtashr3)
{
  run_test_case_test ("smtashr3", ".smt2", "smtashr3");
}

TEST_F (TestTestCases, smtrepeat)
{
  run_test_case_test ("smtrepeat", ".smt2", "smtrepeat");
}

TEST_F (TestTestCases, smtzeroextend)
{
  run_test_case_test ("smtzeroextend", ".smt2", "smtzeroextend");
}

TEST_F (TestTestCases, smtsignextend)
{
  run_test_case_test ("smtsignextend", ".smt2", "smtsignextend");
}

TEST_F (TestTestCases, smtrotate)
{
  run_test_case_test ("smtrotate", ".smt2", "smtrotate");
}

TEST_F (TestTestCases, uremudivaxiom4)
{
  run_test_case_test ("uremudivaxiom4", ".btor", "uremudivaxiom4");
}

TEST_F (TestTestCases, uremudivaxiom4no)
{
  run_test_case_test ("uremudivaxiom4no", ".btor", "uremudivaxiom4no");
}

TEST_F (TestTestCases, regsmod1)
{
  run_test_case_test ("regsmod1", ".smt2", "regsmod1");
}

TEST_F (TestTestCases, regr_5smod3)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt (
      d_btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
  run_test_case_test ("regr-5smod3", ".btor", "regr-5smod3");
}

TEST_F (TestTestCases, regr_5srem3)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt (
      d_btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
  run_test_case_test ("regr-5srem3", ".btor", "regr-5srem3");
}

TEST_F (TestTestCases, regr5smod_3)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt (
      d_btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
  run_test_case_test ("regr5smod-3", ".btor", "regr5smod-3");
}

TEST_F (TestTestCases, regr5srem_3)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt (
      d_btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
  run_test_case_test ("regr5srem-3", ".btor", "regr5srem-3");
}

TEST_F (TestTestCases, regr_6smod3)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt (
      d_btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
  run_test_case_test ("regr-6smod3", ".btor", "regr-6smod3");
}

TEST_F (TestTestCases, regr_6srem3)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt (
      d_btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
  run_test_case_test ("regr-6srem3", ".btor", "regr-6srem3");
}

TEST_F (TestTestCases, regr6smod_3)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt (
      d_btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
  run_test_case_test ("regr6smod-3", ".btor", "regr6smod-3");
}

TEST_F (TestTestCases, regr6srem_3)
{
  d_get_model    = true;
  d_model_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt (
      d_btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
  run_test_case_test ("regr6srem-3", ".btor", "regr6srem-3");
}

TEST_F (TestTestCases, gtewithsub)
{
  run_test_case_test ("gtewithsub", ".btor", "gtewithsub");
}

TEST_F (TestTestCases, smtaxiommccarthy)
{
  run_test_case_test ("smtaxiommccarthy", ".smt2", "smtaxiommccarthy");
}

TEST_F (TestTestCases, mulassoc4)
{
  run_test_case_test ("mulassoc4", ".smt2", "mulassoc4");
}

TEST_F (TestTestCases, mulassoc5)
{
  run_test_case_test ("mulassoc5", ".smt2", "mulassoc5");
}

TEST_F (TestTestCases, mulassoc6)
{
  run_test_case_test ("mulassoc6", ".smt2", "mulassoc6");
}

TEST_F (TestTestCases, udiv8castdown4)
{
  run_test_case_test ("udiv8castdown4", ".btor", "udiv8castdown4");
}

TEST_F (TestTestCases, udiv8castdown5)
{
  run_test_case_test ("udiv8castdown5", ".btor", "udiv8castdown5");
}

TEST_F (TestTestCases, udiv8castdown6)
{
  run_test_case_test ("udiv8castdown6", ".btor", "udiv8castdown6");
}

TEST_F (TestTestCases, udiv8castdown7)
{
  run_test_case_test ("udiv8castdown7", ".btor", "udiv8castdown7");
}

TEST_F (TestTestCases, udiv16castdown8)
{
  run_test_case_test ("udiv16castdown8", ".btor", "udiv16castdown8");
}

TEST_F (TestTestCases, lazyreadwritebug1)
{
  run_test_case_test ("lazyreadwritebug1", ".btor", "lazyreadwritebug1");
}

TEST_F (TestTestCases, arrayanderr)
{
  d_expect_parse_error = true;
  run_test_case_test ("arrayanderr", ".btor", "arrayanderr");
}

TEST_F (TestTestCases, arrayeqerr0)
{
  d_expect_parse_error = true;
  run_test_case_test ("arrayeqerr0", ".btor", "arrayeqerr0");
}

TEST_F (TestTestCases, arrayeqerr1)
{
  d_expect_parse_error = true;
  run_test_case_test ("arrayeqerr1", ".btor", "arrayeqerr1");
}

TEST_F (TestTestCases, arrayeqerr2)
{
  d_expect_parse_error = true;
  run_test_case_test ("arrayeqerr2", ".btor", "arrayeqerr2");
}

TEST_F (TestTestCases, dumpbtor1)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("dumpbtor1", ".btor", "dumpbtor1");
}

// !! currently broken due to dumper support for args/apply
TEST_F (TestTestCases, DISABLED_dumpbtor2)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("dumpbtor2", ".btor", "dumpbtor2");
}

TEST_F (TestTestCases, dumpbtor3)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test ("dumpbtor3", ".btor", "dumpbtor3");
}

TEST_F (TestTestCases, dumpsmt1)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "smt2";
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("dumpsmt1", ".btor", "dumpsmt1");
}

TEST_F (TestTestCases, dumpsmt2)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "smt2";
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("dumpsmt2", ".btor", "dumpsmt2");
}

TEST_F (TestTestCases, smtextarrayaxiom1uf)
{
  run_test_case_test ("smtextarrayaxiom1uf", ".smt2", "smtextarrayaxiom1uf");
}

TEST_F (TestTestCases, smtextarrayaxiom1)
{
  run_test_case_test ("smtextarrayaxiom1", ".smt2", "smtextarrayaxiom1");
}

TEST_F (TestTestCases, smtextarray1sat0)
{
  run_test_case_test ("smtextarray1sat0", ".smt2", "smtextarray1sat0");
}

TEST_F (TestTestCases, smtextarray1sat1)
{
  run_test_case_test ("smtextarray1sat1", ".smt2", "smtextarray1sat1");
}

TEST_F (TestTestCases, smtextarrayaxiom2uf)
{
  run_test_case_test ("smtextarrayaxiom2uf", ".smt2", "smtextarrayaxiom2uf");
}

TEST_F (TestTestCases, smtextarrayaxiom2)
{
  run_test_case_test ("smtextarrayaxiom2", ".smt2", "smtextarrayaxiom2");
}

TEST_F (TestTestCases, smtextarray2sat0)
{
  run_test_case_test ("smtextarray2sat0", ".smt2", "smtextarray2sat0");
}

TEST_F (TestTestCases, smtextarray2sat1)
{
  run_test_case_test ("smtextarray2sat1", ".smt2", "smtextarray2sat1");
}

TEST_F (TestTestCases, smtextarray2sat2)
{
  run_test_case_test ("smtextarray2sat2", ".smt2", "smtextarray2sat2");
}

TEST_F (TestTestCases, smtextarray2sat3)
{
  run_test_case_test ("smtextarray2sat3", ".smt2", "smtextarray2sat3");
}

TEST_F (TestTestCases, smtextarrayaxiom3uf)
{
  run_test_case_test ("smtextarrayaxiom3uf", ".smt2", "smtextarrayaxiom3uf");
}

TEST_F (TestTestCases, smtextarrayaxiom3)
{
  run_test_case_test ("smtextarrayaxiom3", ".smt2", "smtextarrayaxiom3");
}

TEST_F (TestTestCases, smtextarray3sat0)
{
  run_test_case_test ("smtextarray3sat0", ".smt2", "smtextarray3sat0");
}

TEST_F (TestTestCases, smtextarray3sat1)
{
  run_test_case_test ("smtextarray3sat1", ".smt2", "smtextarray3sat1");
}

TEST_F (TestTestCases, smtextarray3sat2)
{
  run_test_case_test ("smtextarray3sat2", ".smt2", "smtextarray3sat2");
}

TEST_F (TestTestCases, smtextarray3sat3)
{
  run_test_case_test ("smtextarray3sat3", ".smt2", "smtextarray3sat3");
}

TEST_F (TestTestCases, smtextarray3sat4)
{
  run_test_case_test ("smtextarray3sat4", ".smt2", "smtextarray3sat4");
}

TEST_F (TestTestCases, smtextarray3sat5)
{
  run_test_case_test ("smtextarray3sat5", ".smt2", "smtextarray3sat5");
}

TEST_F (TestTestCases, smtextarray3sat6)
{
  run_test_case_test ("smtextarray3sat6", ".smt2", "smtextarray3sat6");
}

TEST_F (TestTestCases, smtextarray3sat7)
{
  run_test_case_test ("smtextarray3sat7", ".smt2", "smtextarray3sat7");
}

TEST_F (TestTestCases, smtextarrayaxiom4uf)
{
  run_test_case_test ("smtextarrayaxiom4uf", ".smt2", "smtextarrayaxiom4uf");
}

TEST_F (TestTestCases, smtextarrayaxiom4)
{
  run_test_case_test ("smtextarrayaxiom4", ".smt2", "smtextarrayaxiom4");
}

TEST_F (TestTestCases, extarraywrite1)
{
  run_test_case_test ("extarraywrite1", ".btor", "extarraywrite1");
}

TEST_F (TestTestCases, extarraywrite2)
{
  run_test_case_test ("extarraywrite2", ".btor", "extarraywrite2");
}

TEST_F (TestTestCases, extarraywrite3)
{
  run_test_case_test ("extarraywrite3", ".smt2", "extarraywrite3");
}

TEST_F (TestTestCases, extarraywrite3sat)
{
  run_test_case_test ("extarraywrite3sat", ".smt2", "extarraywrite3sat");
}

TEST_F (TestTestCases, smtarraycond1)
{
  run_test_case_test ("smtarraycond1", ".smt2", "smtarraycond1");
}

TEST_F (TestTestCases, smtarraycond2)
{
  run_test_case_test ("smtarraycond2", ".smt2", "smtarraycond2");
}

TEST_F (TestTestCases, smtarraycond3)
{
  run_test_case_test ("smtarraycond3", ".smt2", "smtarraycond3");
}

TEST_F (TestTestCases, rwpropindexplusconst1)
{
  run_test_case_test (
      "rwpropindexplusconst1", ".btor", "rwpropindexplusconst1");
}

TEST_F (TestTestCases, rwpropindexplusconst2)
{
  run_test_case_test (
      "rwpropindexplusconst2", ".btor", "rwpropindexplusconst2");
}

TEST_F (TestTestCases, rwpropindexplusconst3)
{
  run_test_case_test (
      "rwpropindexplusconst3", ".btor", "rwpropindexplusconst3");
}

TEST_F (TestTestCases, rwpropindexplusconst4)
{
  run_test_case_test (
      "rwpropindexplusconst4", ".btor", "rwpropindexplusconst4");
}

TEST_F (TestTestCases, rwpropindexplusconst1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "rwpropindexplusconst1", ".btor", "rwpropindexplusconst1");
}

TEST_F (TestTestCases, rwpropindexplusconst2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "rwpropindexplusconst2", ".btor", "rwpropindexplusconst2");
}

TEST_F (TestTestCases, rwpropindexplusconst3_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "rwpropindexplusconst3", ".btor", "rwpropindexplusconst3");
}

TEST_F (TestTestCases, rwpropindexplusconst4_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "rwpropindexplusconst4", ".btor", "rwpropindexplusconst4");
}

TEST_F (TestTestCases, rwpropindexpluszero1)
{
  run_test_case_test ("rwpropindexpluszero1", ".btor", "rwpropindexpluszero1");
}

TEST_F (TestTestCases, rwpropindexpluszero2)
{
  run_test_case_test ("rwpropindexpluszero2", ".btor", "rwpropindexpluszero2");
}

TEST_F (TestTestCases, rwpropindexpluszero3)
{
  run_test_case_test ("rwpropindexpluszero3", ".btor", "rwpropindexpluszero3");
}

TEST_F (TestTestCases, rwpropindexpluszero4)
{
  run_test_case_test ("rwpropindexpluszero4", ".btor", "rwpropindexpluszero4");
}

TEST_F (TestTestCases, rwpropindexpluszero5)
{
  run_test_case_test ("rwpropindexpluszero5", ".btor", "rwpropindexpluszero5");
}

TEST_F (TestTestCases, rwpropindexpluszero6)
{
  run_test_case_test ("rwpropindexpluszero6", ".btor", "rwpropindexpluszero6");
}

TEST_F (TestTestCases, rwpropindexpluszero7)
{
  run_test_case_test ("rwpropindexpluszero7", ".btor", "rwpropindexpluszero7");
}

TEST_F (TestTestCases, rwpropindexpluszero8)
{
  run_test_case_test ("rwpropindexpluszero8", ".btor", "rwpropindexpluszero8");
}

TEST_F (TestTestCases, rwpropindexpluszero1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rwpropindexpluszero1", ".btor", "rwpropindexpluszero1");
}

TEST_F (TestTestCases, rwpropindexpluszero2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rwpropindexpluszero2", ".btor", "rwpropindexpluszero2");
}

TEST_F (TestTestCases, rwpropindexpluszero3_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rwpropindexpluszero3", ".btor", "rwpropindexpluszero3");
}

TEST_F (TestTestCases, rwpropindexpluszero4_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rwpropindexpluszero4", ".btor", "rwpropindexpluszero4");
}

TEST_F (TestTestCases, rwpropindexpluszero5_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rwpropindexpluszero5", ".btor", "rwpropindexpluszero5");
}

TEST_F (TestTestCases, rwpropindexpluszero6_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rwpropindexpluszero6", ".btor", "rwpropindexpluszero6");
}

TEST_F (TestTestCases, rwpropindexpluszero7_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rwpropindexpluszero7", ".btor", "rwpropindexpluszero7");
}

TEST_F (TestTestCases, rwpropindexpluszero8_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rwpropindexpluszero8", ".btor", "rwpropindexpluszero8");
}

TEST_F (TestTestCases, arraycondconst)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("arraycondconst", ".btor", "arraycondconst");
}

TEST_F (TestTestCases, arraycondconstaig)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("arraycondconstaig", ".btor", "arraycondconstaig");
}

TEST_F (TestTestCases, random1)
{
  run_test_case_test ("random1", ".btor", "random1");
}

TEST_F (TestTestCases, random1btor2)
{
  run_test_case_test ("random1", ".btor2", "random1btor2");
}

TEST_F (TestTestCases, random2)
{
  run_test_case_test ("random2", ".btor", "random2");
}

TEST_F (TestTestCases, random3)
{
  run_test_case_test ("random3", ".btor", "random3");
}

TEST_F (TestTestCases, random4)
{
  run_test_case_test ("random4", ".btor", "random4");
}

TEST_F (TestTestCases, random5_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("random5", ".btor", "random5");
}

TEST_F (TestTestCases, random5_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("random5", ".btor", "random5");
}

TEST_F (TestTestCases, rw16_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw16", ".btor", "rw16");
}

TEST_F (TestTestCases, rw16_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw16", ".btor", "rw16");
}

TEST_F (TestTestCases, rw17_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw17", ".btor", "rw17");
}

TEST_F (TestTestCases, rw17_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw17", ".btor", "rw17");
}

TEST_F (TestTestCases, rw18_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw18", ".btor", "rw18");
}

TEST_F (TestTestCases, rw18_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw18", ".btor", "rw18");
}

TEST_F (TestTestCases, rw19_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw19", ".btor", "rw19");
}

TEST_F (TestTestCases, rw19_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw19", ".btor", "rw19");
}

TEST_F (TestTestCases, rw20_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw20", ".btor", "rw20");
}

TEST_F (TestTestCases, rw20_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw20", ".btor", "rw20");
}

TEST_F (TestTestCases, rw21_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw21", ".btor", "rw21");
}

TEST_F (TestTestCases, rw21_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw21", ".btor", "rw21");
}

TEST_F (TestTestCases, rw22_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw22", ".btor", "rw22");
}

TEST_F (TestTestCases, rw22_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw22", ".btor", "rw22");
}

TEST_F (TestTestCases, rw23_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw23", ".btor", "rw23");
}

TEST_F (TestTestCases, rw23_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw23", ".btor", "rw23");
}

TEST_F (TestTestCases, rw24_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw24", ".btor", "rw24");
}

TEST_F (TestTestCases, rw24_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw24", ".btor", "rw24");
}

TEST_F (TestTestCases, rw25_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw25", ".btor", "rw25");
}

TEST_F (TestTestCases, rw25_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw25", ".btor", "rw25");
}

TEST_F (TestTestCases, rw26_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw26", ".btor", "rw26");
}

TEST_F (TestTestCases, rw26_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw26", ".btor", "rw26");
}

TEST_F (TestTestCases, rw27_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw27", ".btor", "rw27");
}

TEST_F (TestTestCases, rw27_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw27", ".btor", "rw27");
}

TEST_F (TestTestCases, rw28_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw28", ".btor", "rw28");
}

TEST_F (TestTestCases, rw28_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw28", ".btor", "rw28");
}

TEST_F (TestTestCases, rw29_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw29", ".btor", "rw29");
}

TEST_F (TestTestCases, rw29_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw29", ".btor", "rw29");
}

TEST_F (TestTestCases, rw30_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw30", ".btor", "rw30");
}

TEST_F (TestTestCases, rw30_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw30", ".btor", "rw30");
}

TEST_F (TestTestCases, rw31_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw31", ".btor", "rw31");
}

TEST_F (TestTestCases, rw31_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw31", ".btor", "rw31");
}

TEST_F (TestTestCases, rw32_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw32", ".btor", "rw32");
}

TEST_F (TestTestCases, rw32_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw32", ".btor", "rw32");
}

TEST_F (TestTestCases, rw33_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw33", ".btor", "rw33");
}

TEST_F (TestTestCases, rw33_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw33", ".btor", "rw33");
}

TEST_F (TestTestCases, rw34_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw34", ".btor", "rw34");
}

TEST_F (TestTestCases, rw34_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw34", ".btor", "rw34");
}

TEST_F (TestTestCases, rw35_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw35", ".btor", "rw35");
}

TEST_F (TestTestCases, rw35_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw35", ".btor", "rw35");
}

TEST_F (TestTestCases, rw36_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw36", ".btor", "rw36");
}

TEST_F (TestTestCases, rw36_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw36", ".btor", "rw36");
}

TEST_F (TestTestCases, rw37_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw37", ".btor", "rw37");
}

TEST_F (TestTestCases, rw37_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw37", ".btor", "rw37");
}

TEST_F (TestTestCases, rw38_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw38", ".btor", "rw38");
}

TEST_F (TestTestCases, rw38_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw38", ".btor", "rw38");
}

TEST_F (TestTestCases, rw39_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw39", ".btor", "rw39");
}

TEST_F (TestTestCases, rw39_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw39", ".btor", "rw39");
}

TEST_F (TestTestCases, rw40_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw40", ".btor", "rw40");
}

TEST_F (TestTestCases, rw40_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw40", ".btor", "rw40");
}

TEST_F (TestTestCases, rw41_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw41", ".btor", "rw41");
}

TEST_F (TestTestCases, rw41_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw41", ".btor", "rw41");
}

TEST_F (TestTestCases, rw42_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw42", ".btor", "rw42");
}

TEST_F (TestTestCases, rw42_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw42", ".btor", "rw42");
}

TEST_F (TestTestCases, rw43_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw43", ".btor", "rw43");
}

TEST_F (TestTestCases, rw43_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw43", ".btor", "rw43");
}

TEST_F (TestTestCases, rw44_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw44", ".btor", "rw44");
}

TEST_F (TestTestCases, rw44_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw44", ".btor", "rw44");
}

TEST_F (TestTestCases, rw45_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw45", ".btor", "rw45");
}

TEST_F (TestTestCases, rw45_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw45", ".btor", "rw45");
}

TEST_F (TestTestCases, rw46) { run_test_case_test ("rw46", ".btor", "rw46"); }

TEST_F (TestTestCases, rw47) { run_test_case_test ("rw47", ".btor", "rw47"); }

TEST_F (TestTestCases, rw48) { run_test_case_test ("rw48", ".btor", "rw48"); }

TEST_F (TestTestCases, rw49) { run_test_case_test ("rw49", ".btor", "rw49"); }

TEST_F (TestTestCases, rw50) { run_test_case_test ("rw50", ".btor", "rw50"); }

TEST_F (TestTestCases, rw51) { run_test_case_test ("rw51", ".btor", "rw51"); }

TEST_F (TestTestCases, rw52_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw52", ".btor", "rw52");
}

TEST_F (TestTestCases, rw52_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw52", ".btor", "rw52");
}

TEST_F (TestTestCases, rw53_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw53", ".btor", "rw53");
}

TEST_F (TestTestCases, rw53_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw53", ".btor", "rw53");
}

TEST_F (TestTestCases, rw54_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw54", ".btor", "rw54");
}

TEST_F (TestTestCases, rw54_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw54", ".btor", "rw54");
}

TEST_F (TestTestCases, rw55_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw55", ".btor", "rw55");
}

TEST_F (TestTestCases, rw55_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw55", ".btor", "rw55");
}

TEST_F (TestTestCases, rw56_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw56", ".btor", "rw56");
}

TEST_F (TestTestCases, rw56_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw56", ".btor", "rw56");
}

TEST_F (TestTestCases, rw57_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw57", ".btor", "rw57");
}

TEST_F (TestTestCases, rw57_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw57", ".btor", "rw57");
}

TEST_F (TestTestCases, rw58_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw58", ".btor", "rw58");
}

TEST_F (TestTestCases, rw58_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw58", ".btor", "rw58");
}

TEST_F (TestTestCases, rw59_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw59", ".btor", "rw59");
}

TEST_F (TestTestCases, rw59_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw59", ".btor", "rw59");
}

TEST_F (TestTestCases, rw60) { run_test_case_test ("rw60", ".btor", "rw60"); }

TEST_F (TestTestCases, rw61_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw61", ".btor", "rw61");
}

TEST_F (TestTestCases, rw61_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw61", ".btor", "rw61");
}

TEST_F (TestTestCases, rw62_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw62", ".btor", "rw62");
}

TEST_F (TestTestCases, rw62_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw62", ".btor", "rw62");
}

TEST_F (TestTestCases, rw63_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw63", ".btor", "rw63");
}

TEST_F (TestTestCases, rw63_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw63", ".btor", "rw63");
}

TEST_F (TestTestCases, rw64_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw64", ".btor", "rw64");
}

TEST_F (TestTestCases, rw64_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw64", ".btor", "rw64");
}

TEST_F (TestTestCases, rw65_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw65", ".btor", "rw65");
}

TEST_F (TestTestCases, rw65_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw65", ".btor", "rw65");
}

TEST_F (TestTestCases, rw66_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw66", ".btor", "rw66");
}

TEST_F (TestTestCases, rw66_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw66", ".btor", "rw66");
}

TEST_F (TestTestCases, rw67_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw67", ".btor", "rw67");
}

TEST_F (TestTestCases, rw67_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw67", ".btor", "rw67");
}

TEST_F (TestTestCases, rw68_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw68", ".btor", "rw68");
}

TEST_F (TestTestCases, rw68_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw68", ".btor", "rw68");
}

TEST_F (TestTestCases, rw69_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw69", ".btor", "rw69");
}

TEST_F (TestTestCases, rw69_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw69", ".btor", "rw69");
}

TEST_F (TestTestCases, rw70_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw70", ".btor", "rw70");
}

TEST_F (TestTestCases, rw70_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw70", ".btor", "rw70");
}

TEST_F (TestTestCases, rw71_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw71", ".btor", "rw71");
}

TEST_F (TestTestCases, rw71_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw71", ".btor", "rw71");
}

TEST_F (TestTestCases, rw72_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw72", ".btor", "rw72");
}

TEST_F (TestTestCases, rw72_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw72", ".btor", "rw72");
}

TEST_F (TestTestCases, rw73_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw73", ".btor", "rw73");
}

TEST_F (TestTestCases, rw73_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw73", ".btor", "rw73");
}

TEST_F (TestTestCases, rw74_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw74", ".btor", "rw74");
}

TEST_F (TestTestCases, rw74_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw74", ".btor", "rw74");
}

TEST_F (TestTestCases, rw75_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw75", ".btor", "rw75");
}

TEST_F (TestTestCases, rw75_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw75", ".btor", "rw75");
}

TEST_F (TestTestCases, rw76_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw76", ".btor", "rw76");
}

TEST_F (TestTestCases, rw76_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw76", ".btor", "rw76");
}

TEST_F (TestTestCases, rw77_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw77", ".btor", "rw77");
}

TEST_F (TestTestCases, rw77_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw77", ".btor", "rw77");
}

TEST_F (TestTestCases, rw78_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw78", ".btor", "rw78");
}

TEST_F (TestTestCases, rw78_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw78", ".btor", "rw78");
}

TEST_F (TestTestCases, rw79_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw79", ".btor", "rw79");
}

TEST_F (TestTestCases, rw79_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw79", ".btor", "rw79");
}

TEST_F (TestTestCases, rw80_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw80", ".btor", "rw80");
}

TEST_F (TestTestCases, rw80_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw80", ".btor", "rw80");
}

TEST_F (TestTestCases, rw81_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw81", ".btor", "rw81");
}

TEST_F (TestTestCases, rw81_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw81", ".btor", "rw81");
}

TEST_F (TestTestCases, rw82_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw82", ".btor", "rw82");
}

TEST_F (TestTestCases, rw82_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw82", ".btor", "rw82");
}

TEST_F (TestTestCases, rw83_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw83", ".btor", "rw83");
}

TEST_F (TestTestCases, rw83_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw83", ".btor", "rw83");
}

TEST_F (TestTestCases, rw84_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw84", ".btor", "rw84");
}

TEST_F (TestTestCases, rw84_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw84", ".btor", "rw84");
}

TEST_F (TestTestCases, rw85_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw85", ".btor", "rw85");
}

TEST_F (TestTestCases, rw85_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw85", ".btor", "rw85");
}

TEST_F (TestTestCases, rw86_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw86", ".btor", "rw86");
}

TEST_F (TestTestCases, rw86_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw86", ".btor", "rw86");
}

TEST_F (TestTestCases, rw87_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw87", ".btor", "rw87");
}

TEST_F (TestTestCases, rw87_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw87", ".btor", "rw87");
}

TEST_F (TestTestCases, rw88_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw88", ".btor", "rw88");
}

TEST_F (TestTestCases, rw88_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw88", ".btor", "rw88");
}

TEST_F (TestTestCases, rw89_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw89", ".btor", "rw89");
}

TEST_F (TestTestCases, rw89_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw89", ".btor", "rw89");
}

TEST_F (TestTestCases, rw90_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw90", ".btor", "rw90");
}

TEST_F (TestTestCases, rw90_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw90", ".btor", "rw90");
}

TEST_F (TestTestCases, rw91_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw91", ".btor", "rw91");
}

TEST_F (TestTestCases, rw91_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw91", ".btor", "rw91");
}

TEST_F (TestTestCases, rw92_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw92", ".btor", "rw92");
}

TEST_F (TestTestCases, rw92_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw92", ".btor", "rw92");
}

TEST_F (TestTestCases, rw93_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw93", ".btor", "rw93");
}

TEST_F (TestTestCases, rw93_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw93", ".btor", "rw93");
}

TEST_F (TestTestCases, rw94_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw94", ".btor", "rw94");
}

TEST_F (TestTestCases, rw94_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw94", ".btor", "rw94");
}

TEST_F (TestTestCases, rw95_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw95", ".btor", "rw95");
}

TEST_F (TestTestCases, rw95_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw95", ".btor", "rw95");
}

TEST_F (TestTestCases, rw96_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw96", ".btor", "rw96");
}

TEST_F (TestTestCases, rw96_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw96", ".btor", "rw96");
}

TEST_F (TestTestCases, rw97_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw97", ".btor", "rw97");
}

TEST_F (TestTestCases, rw97_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw97", ".btor", "rw97");
}

TEST_F (TestTestCases, rw98_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw98", ".btor", "rw98");
}

TEST_F (TestTestCases, rw98_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw98", ".btor", "rw98");
}

TEST_F (TestTestCases, rw99_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw99", ".btor", "rw99");
}

TEST_F (TestTestCases, rw99_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw99", ".btor", "rw99");
}

TEST_F (TestTestCases, rw100_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw100", ".btor", "rw100");
}

TEST_F (TestTestCases, rw100_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw100", ".btor", "rw100");
}

TEST_F (TestTestCases, rw101_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw101", ".btor", "rw101");
}

TEST_F (TestTestCases, rw101_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw101", ".btor", "rw101");
}

TEST_F (TestTestCases, rw102_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw102", ".btor", "rw102");
}

TEST_F (TestTestCases, rw102_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw102", ".btor", "rw102");
}

TEST_F (TestTestCases, rw103_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw103", ".btor", "rw103");
}

TEST_F (TestTestCases, rw103_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw103", ".btor", "rw103");
}

TEST_F (TestTestCases, rw104_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw104", ".btor", "rw104");
}

TEST_F (TestTestCases, rw104_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw104", ".btor", "rw104");
}

TEST_F (TestTestCases, rw105_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw105", ".btor", "rw105");
}

TEST_F (TestTestCases, rw105_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw105", ".btor", "rw105");
}

TEST_F (TestTestCases, rw106_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw106", ".btor", "rw106");
}

TEST_F (TestTestCases, rw106_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw106", ".btor", "rw106");
}

TEST_F (TestTestCases, rw107_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw107", ".btor", "rw107");
}

TEST_F (TestTestCases, rw107_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw107", ".btor", "rw107");
}

TEST_F (TestTestCases, rw108_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw108", ".btor", "rw108");
}

TEST_F (TestTestCases, rw108_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw108", ".btor", "rw108");
}

TEST_F (TestTestCases, rw109_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw109", ".btor", "rw109");
}

TEST_F (TestTestCases, rw109_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw109", ".btor", "rw109");
}

TEST_F (TestTestCases, rw110_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw110", ".btor", "rw110");
}

TEST_F (TestTestCases, rw110_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw110", ".btor", "rw110");
}

TEST_F (TestTestCases, rw111_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw111", ".btor", "rw111");
}

TEST_F (TestTestCases, rw111_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw111", ".btor", "rw111");
}

TEST_F (TestTestCases, rw112_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw112", ".btor", "rw112");
}

TEST_F (TestTestCases, rw112_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw112", ".btor", "rw112");
}

TEST_F (TestTestCases, rw113_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw113", ".btor", "rw113");
}

TEST_F (TestTestCases, rw113_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw113", ".btor", "rw113");
}

TEST_F (TestTestCases, rw114_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw114", ".btor", "rw114");
}

TEST_F (TestTestCases, rw114_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw114", ".btor", "rw114");
}

TEST_F (TestTestCases, rw115_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw115", ".btor", "rw115");
}

TEST_F (TestTestCases, rw115_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw115", ".btor", "rw115");
}

TEST_F (TestTestCases, rw116_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw116", ".btor", "rw116");
}

TEST_F (TestTestCases, rw116_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw116", ".btor", "rw116");
}

TEST_F (TestTestCases, rw117_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw117", ".btor", "rw117");
}

TEST_F (TestTestCases, rw117_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw117", ".btor", "rw117");
}

TEST_F (TestTestCases, rw118_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw118", ".btor", "rw118");
}

TEST_F (TestTestCases, rw118_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw118", ".btor", "rw118");
}

TEST_F (TestTestCases, rw119_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw119", ".btor", "rw119");
}

TEST_F (TestTestCases, rw119_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw119", ".btor", "rw119");
}

TEST_F (TestTestCases, rw120_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw120", ".btor", "rw120");
}

TEST_F (TestTestCases, rw120_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw120", ".btor", "rw120");
}

TEST_F (TestTestCases, rw121_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw121", ".btor", "rw121");
}

TEST_F (TestTestCases, rw121_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw121", ".btor", "rw121");
}

TEST_F (TestTestCases, rw122_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw122", ".btor", "rw122");
}

TEST_F (TestTestCases, rw122_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw122", ".btor", "rw122");
}

TEST_F (TestTestCases, rw123_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw123", ".btor", "rw123");
}

TEST_F (TestTestCases, rw123_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw123", ".btor", "rw123");
}

TEST_F (TestTestCases, rw124_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw124", ".btor", "rw124");
}

TEST_F (TestTestCases, rw124_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw124", ".btor", "rw124");
}

TEST_F (TestTestCases, rw125_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw125", ".btor", "rw125");
}

TEST_F (TestTestCases, rw125_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw125", ".btor", "rw125");
}

TEST_F (TestTestCases, rw126_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw126", ".btor", "rw126");
}

TEST_F (TestTestCases, rw126_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw126", ".btor", "rw126");
}

TEST_F (TestTestCases, rw127_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw127", ".btor", "rw127");
}

TEST_F (TestTestCases, rw127_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw127", ".btor", "rw127");
}

TEST_F (TestTestCases, rw128_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw128", ".btor", "rw128");
}

TEST_F (TestTestCases, rw128_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw128", ".btor", "rw128");
}

TEST_F (TestTestCases, rw129_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw129", ".btor", "rw129");
}

TEST_F (TestTestCases, rw129_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw129", ".btor", "rw129");
}

TEST_F (TestTestCases, rw130_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw130", ".btor", "rw130");
}

TEST_F (TestTestCases, rw130_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw130", ".btor", "rw130");
}

TEST_F (TestTestCases, rw131_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw131", ".btor", "rw131");
}

TEST_F (TestTestCases, rw131_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw131", ".btor", "rw131");
}

TEST_F (TestTestCases, rw132_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw132", ".btor", "rw132");
}

TEST_F (TestTestCases, rw132_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw132", ".btor", "rw132");
}

TEST_F (TestTestCases, rw133_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw133", ".btor", "rw133");
}

TEST_F (TestTestCases, rw133_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw133", ".btor", "rw133");
}

TEST_F (TestTestCases, rw134_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw134", ".btor", "rw134");
}

TEST_F (TestTestCases, rw134_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw134", ".btor", "rw134");
}

TEST_F (TestTestCases, rw135_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw135", ".btor", "rw135");
}

TEST_F (TestTestCases, rw135_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw135", ".btor", "rw135");
}

TEST_F (TestTestCases, rw136_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw136", ".btor", "rw136");
}

TEST_F (TestTestCases, rw136_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw136", ".btor", "rw136");
}

TEST_F (TestTestCases, rw137_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw137", ".btor", "rw137");
}

TEST_F (TestTestCases, rw137_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw137", ".btor", "rw137");
}

TEST_F (TestTestCases, rw138_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw138", ".btor", "rw138");
}

TEST_F (TestTestCases, rw138_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw138", ".btor", "rw138");
}

TEST_F (TestTestCases, rw139_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw139", ".btor", "rw139");
}

TEST_F (TestTestCases, rw139_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw139", ".btor", "rw139");
}

TEST_F (TestTestCases, rw140_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw140", ".btor", "rw140");
}

TEST_F (TestTestCases, rw140_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw140", ".btor", "rw140");
}

TEST_F (TestTestCases, rw141_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw141", ".btor", "rw141");
}

TEST_F (TestTestCases, rw141_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw141", ".btor", "rw141");
}

TEST_F (TestTestCases, rw142_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw142", ".btor", "rw142");
}

TEST_F (TestTestCases, rw142_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw142", ".btor", "rw142");
}

TEST_F (TestTestCases, rw143_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw143", ".btor", "rw143");
}

TEST_F (TestTestCases, rw143_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw143", ".btor", "rw143");
}

TEST_F (TestTestCases, rw144_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw144", ".btor", "rw144");
}

TEST_F (TestTestCases, rw144_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw144", ".btor", "rw144");
}

TEST_F (TestTestCases, rw145_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw145", ".btor", "rw145");
}

TEST_F (TestTestCases, rw145_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw145", ".btor", "rw145");
}

TEST_F (TestTestCases, rw146_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw146", ".btor", "rw146");
}

TEST_F (TestTestCases, rw146_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw146", ".btor", "rw146");
}

TEST_F (TestTestCases, rw147_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw147", ".btor", "rw147");
}

TEST_F (TestTestCases, rw147_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw147", ".btor", "rw147");
}

TEST_F (TestTestCases, rw148_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw148", ".btor", "rw148");
}

TEST_F (TestTestCases, rw148_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw148", ".btor", "rw148");
}

TEST_F (TestTestCases, rw149_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw149", ".btor", "rw149");
}

TEST_F (TestTestCases, rw149_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw149", ".btor", "rw149");
}

TEST_F (TestTestCases, rw150_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw150", ".btor", "rw150");
}

TEST_F (TestTestCases, rw150_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw150", ".btor", "rw150");
}

TEST_F (TestTestCases, rw151_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw151", ".btor", "rw151");
}

TEST_F (TestTestCases, rw151_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw151", ".btor", "rw151");
}

TEST_F (TestTestCases, rw152_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw152", ".btor", "rw152");
}

TEST_F (TestTestCases, rw152_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw152", ".btor", "rw152");
}

TEST_F (TestTestCases, rw153_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw153", ".btor", "rw153");
}

TEST_F (TestTestCases, rw153_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw153", ".btor", "rw153");
}

TEST_F (TestTestCases, rw154_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw154", ".btor", "rw154");
}

TEST_F (TestTestCases, rw154_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw154", ".btor", "rw154");
}

TEST_F (TestTestCases, rw155_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw155", ".btor", "rw155");
}

TEST_F (TestTestCases, rw155_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw155", ".btor", "rw155");
}

TEST_F (TestTestCases, rw156_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("rw156", ".btor", "rw156");
}

TEST_F (TestTestCases, rw156_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw156", ".btor", "rw156");
}

TEST_F (TestTestCases, rw157)
{
  run_test_case_test ("rw157", ".btor", "rw157");
}

TEST_F (TestTestCases, rw158)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw158", ".btor", "rw158");
}

TEST_F (TestTestCases, rw159)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw159", ".btor", "rw159");
}

TEST_F (TestTestCases, rw160)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw160", ".btor", "rw160");
}

TEST_F (TestTestCases, rw161)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw161", ".btor", "rw161");
}

TEST_F (TestTestCases, rw162)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw162", ".btor", "rw162");
}

TEST_F (TestTestCases, rw163)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw163", ".btor", "rw163");
}

TEST_F (TestTestCases, rw164)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw164", ".btor", "rw164");
}

TEST_F (TestTestCases, rw165)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw165", ".btor", "rw165");
}

TEST_F (TestTestCases, rw166)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw166", ".btor", "rw166");
}

TEST_F (TestTestCases, rw167)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw167", ".btor", "rw167");
}

TEST_F (TestTestCases, rw168)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw168", ".btor", "rw168");
}

TEST_F (TestTestCases, rw169)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw169", ".btor", "rw169");
}

TEST_F (TestTestCases, rw170)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw170", ".btor", "rw170");
}

TEST_F (TestTestCases, rw171)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw171", ".btor", "rw171");
}

TEST_F (TestTestCases, rw172)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw172", ".btor", "rw172");
}

TEST_F (TestTestCases, rw173)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw173", ".btor", "rw173");
}

TEST_F (TestTestCases, rw174)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw174", ".btor", "rw174");
}

TEST_F (TestTestCases, rw175)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw175", ".btor", "rw175");
}

TEST_F (TestTestCases, rw176)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw176", ".btor", "rw176");
}

TEST_F (TestTestCases, rw177)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("rw177", ".btor", "rw177");
}

TEST_F (TestTestCases, rw178)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw178", ".btor", "rw178");
}

TEST_F (TestTestCases, rw179)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw179", ".btor", "rw179");
}

TEST_F (TestTestCases, rw180)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw180", ".btor", "rw180");
}

TEST_F (TestTestCases, rw181)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw181", ".btor", "rw181");
}

TEST_F (TestTestCases, rw182)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw182", ".btor", "rw182");
}

TEST_F (TestTestCases, rw183)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw183", ".btor", "rw183");
}

TEST_F (TestTestCases, rw184)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw184", ".btor", "rw184");
}

TEST_F (TestTestCases, rw185)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw185", ".btor", "rw185");
}

TEST_F (TestTestCases, rw186)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw186", ".btor", "rw186");
}

TEST_F (TestTestCases, rw187)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw187", ".btor", "rw187");
}

TEST_F (TestTestCases, rw188)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw188", ".btor", "rw188");
}

TEST_F (TestTestCases, rw189)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw189", ".btor", "rw189");
}

TEST_F (TestTestCases, rw190)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw190", ".btor", "rw190");
}

TEST_F (TestTestCases, rw191)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw191", ".btor", "rw191");
}

TEST_F (TestTestCases, rw192)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw192", ".btor", "rw192");
}

TEST_F (TestTestCases, rw193)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw193", ".btor", "rw193");
}

TEST_F (TestTestCases, rw194)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw194", ".btor", "rw194");
}

TEST_F (TestTestCases, rw195)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw195", ".btor", "rw195");
}

TEST_F (TestTestCases, rw196)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw196", ".btor", "rw196");
}

TEST_F (TestTestCases, rw197)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw197", ".btor", "rw197");
}

TEST_F (TestTestCases, rw198)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw198", ".btor", "rw198");
}

TEST_F (TestTestCases, rw199)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw199", ".btor", "rw199");
}

TEST_F (TestTestCases, rw200)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw200", ".btor", "rw200");
}

TEST_F (TestTestCases, rw201)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw201", ".btor", "rw201");
}

TEST_F (TestTestCases, rw202)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw202", ".btor", "rw202");
}

TEST_F (TestTestCases, rw203)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw203", ".btor", "rw203");
}

TEST_F (TestTestCases, rw204)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw204", ".btor", "rw204");
}

TEST_F (TestTestCases, rw205)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw205", ".btor", "rw205");
}

TEST_F (TestTestCases, rw206)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw206", ".btor", "rw206");
}

TEST_F (TestTestCases, rw207)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw207", ".btor", "rw207");
}

TEST_F (TestTestCases, rw208)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw208", ".btor", "rw208");
}

TEST_F (TestTestCases, rw209)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw209", ".btor", "rw209");
}

TEST_F (TestTestCases, rw210)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw210", ".btor", "rw210");
}

TEST_F (TestTestCases, rw211)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw211", ".btor", "rw211");
}

TEST_F (TestTestCases, rw212)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw212", ".smt2", "rw212");
}

TEST_F (TestTestCases, rw213)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw213", ".smt2", "rw213");
}

TEST_F (TestTestCases, rw214)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw214", ".smt2", "rw214");
}

TEST_F (TestTestCases, rw215)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw215", ".smt2", "rw215");
}

TEST_F (TestTestCases, rw216)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw216", ".smt2", "rw216");
}

TEST_F (TestTestCases, rw217)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw217", ".smt2", "rw217");
}

TEST_F (TestTestCases, rw218)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw218", ".smt2", "rw218");
}

TEST_F (TestTestCases, rw219)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw219", ".smt2", "rw219");
}

TEST_F (TestTestCases, rw220)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw220", ".smt2", "rw220");
}

TEST_F (TestTestCases, rw221)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rw221", ".smt2", "rw221");
}

TEST_F (TestTestCases, rww1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("rww1", ".btor", "rww1");
}

TEST_F (TestTestCases, rwr1)
{
  boolector_set_opt (d_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
  run_test_case_test ("rwr1", ".btor", "rwr1");
}

TEST_F (TestTestCases, hd1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd1", ".btor", "hd1");
}

TEST_F (TestTestCases, hd1_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd1", ".btor", "hd1");
}

TEST_F (TestTestCases, hd2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd2", ".btor", "hd2");
}

TEST_F (TestTestCases, hd2_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd2", ".btor", "hd2");
}

TEST_F (TestTestCases, hd3_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd3", ".btor", "hd3");
}

TEST_F (TestTestCases, hd3_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd3", ".btor", "hd3");
}

TEST_F (TestTestCases, hd4_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd4", ".btor", "hd4");
}

TEST_F (TestTestCases, hd4_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd4", ".btor", "hd4");
}

TEST_F (TestTestCases, hd5_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd5", ".btor", "hd5");
}

TEST_F (TestTestCases, hd5_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd5", ".btor", "hd5");
}

TEST_F (TestTestCases, hd6_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd6", ".btor", "hd6");
}

TEST_F (TestTestCases, hd6_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd6", ".btor", "hd6");
}

TEST_F (TestTestCases, hd7_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd7", ".btor", "hd7");
}

TEST_F (TestTestCases, hd7_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd7", ".btor", "hd7");
}

TEST_F (TestTestCases, hd8_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd8", ".btor", "hd8");
}

TEST_F (TestTestCases, hd8_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd8", ".btor", "hd8");
}

TEST_F (TestTestCases, hd9_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd9", ".btor", "hd9");
}

TEST_F (TestTestCases, hd9_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd9", ".btor", "hd9");
}

TEST_F (TestTestCases, hd10_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd10", ".btor", "hd10");
}

TEST_F (TestTestCases, hd10_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd10", ".btor", "hd10");
}

TEST_F (TestTestCases, hd11_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd11", ".btor", "hd11");
}

TEST_F (TestTestCases, hd11_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd11", ".btor", "hd11");
}

TEST_F (TestTestCases, hd12_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd12", ".btor", "hd12");
}

TEST_F (TestTestCases, hd12_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd12", ".btor", "hd12");
}

TEST_F (TestTestCases, hd13_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd13", ".btor", "hd13");
}

TEST_F (TestTestCases, hd13_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd13", ".btor", "hd13");
}

TEST_F (TestTestCases, hd14_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd14", ".btor", "hd14");
}

TEST_F (TestTestCases, hd14_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd14", ".btor", "hd14");
}

TEST_F (TestTestCases, hd15_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd15", ".btor", "hd15");
}

TEST_F (TestTestCases, hd15_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd15", ".btor", "hd15");
}

TEST_F (TestTestCases, hd16_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd16", ".btor", "hd16");
}

TEST_F (TestTestCases, hd16_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd16", ".btor", "hd16");
}

TEST_F (TestTestCases, hd17_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd17", ".btor", "hd17");
}

TEST_F (TestTestCases, hd17_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd17", ".btor", "hd17");
}

TEST_F (TestTestCases, hd18_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("hd18", ".btor", "hd18");
}

TEST_F (TestTestCases, hd18_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("hd18", ".btor", "hd18");
}

TEST_F (TestTestCases, hd19) { run_test_case_test ("hd19", ".btor", "hd19"); }

TEST_F (TestTestCases, hd20) { run_test_case_test ("hd20", ".btor", "hd20"); }

TEST_F (TestTestCases, hd21) { run_test_case_test ("hd21", ".btor", "hd21"); }

TEST_F (TestTestCases, proxybug)
{
  run_test_case_test ("proxybug", ".btor", "proxybug");
}

TEST_F (TestTestCases, prim8bugreduced)
{
  run_test_case_test ("prim8bugreduced", ".btor", "prim8bugreduced");
}

TEST_F (TestTestCases, bubsort002un)
{
  run_test_case_test ("bubsort002un", ".smt2", "bubsort002un");
}

TEST_F (TestTestCases, selsort002un)
{
  run_test_case_test ("selsort002un", ".smt2", "selsort002un");
}

TEST_F (TestTestCases, swapmem002se)
{
  run_test_case_test ("swapmem002se", ".smt2", "swapmem002se");
}

TEST_F (TestTestCases, swapmem002ue)
{
  run_test_case_test ("swapmem002ue", ".smt2", "swapmem002ue");
}

TEST_F (TestTestCases, wchains002se)
{
  run_test_case_test ("wchains002se", ".smt2", "wchains002se");
}

TEST_F (TestTestCases, wchains002ue)
{
  run_test_case_test ("wchains002ue", ".smt2", "wchains002ue");
}

TEST_F (TestTestCases, dubreva002ue)
{
  run_test_case_test ("dubreva002ue", ".smt2", "dubreva002ue");
}

TEST_F (TestTestCases, binarysearch32s016)
{
  run_test_case_test ("binarysearch32s016", ".smt2", "binarysearch32s016");
}

TEST_F (TestTestCases, count02inc)
{
  run_test_case_test ("count02inc", ".smt2", "count02inc");
}

TEST_F (TestTestCases, count02incuns)
{
  run_test_case_test ("count02incuns", ".smt2", "count02incuns");
}

TEST_F (TestTestCases, count03to6)
{
  run_test_case_test ("count03to6", ".smt2", "count03to6");
}

TEST_F (TestTestCases, count03inc)
{
  run_test_case_test ("count03inc", ".smt2", "count03inc");
}

TEST_F (TestTestCases, count03plus2inc)
{
  run_test_case_test ("count03plus2inc", ".smt2", "count03plus2inc");
}

TEST_F (TestTestCases, countbits016)
{
  run_test_case_test ("countbits016", ".smt2", "countbits016");
}

TEST_F (TestTestCases, fifo32bc04k05)
{
  run_test_case_test ("fifo32bc04k05", ".smt2", "fifo32bc04k05");
}

TEST_F (TestTestCases, fifo32ia04k05)
{
  run_test_case_test ("fifo32ia04k05", ".smt2", "fifo32ia04k05");
}

TEST_F (TestTestCases, fifo32in04k05)
{
  run_test_case_test ("fifo32in04k05", ".smt2", "fifo32in04k05");
}

TEST_F (TestTestCases, nextpoweroftwo016)
{
  run_test_case_test ("nextpoweroftwo016", ".smt2", "nextpoweroftwo016");
}

TEST_F (TestTestCases, memcpy02)
{
  run_test_case_test ("memcpy02", ".smt2", "memcpy02");
}

TEST_F (TestTestCases, regrw8simp)
{
  run_test_case_test ("regrw8simp", ".btor", "regrw8simp");
}

TEST_F (TestTestCases, regprim11simp)
{
  run_test_case_test ("regprim11simp", ".btor", "regprim11simp");
}

TEST_F (TestTestCases, DISABLED_regexit0basic)
{
  run_test_case_test ("regexit0basic", ".btor", "regexit0basic");
}

TEST_F (TestTestCases, DISABLED_nextcounter1)
{
  run_test_case_test ("nextcounter1", ".btor", "nextcounter1");
}

TEST_F (TestTestCases, DISABLED_nextcounter2)
{
  run_test_case_test ("nextcounter2", ".btor", "nextcounter2");
}

TEST_F (TestTestCases, DISABLED_nextcounter3)
{
  run_test_case_test ("nextcounter3", ".btor", "nextcounter3");
}

TEST_F (TestTestCases, DISABLED_nextcounter4)
{
  run_test_case_test ("nextcounter4", ".btor", "nextcounter4");
}

TEST_F (TestTestCases, DISABLED_nextcounter5)
{
  run_test_case_test ("nextcounter5", ".btor", "nextcounter5");
}

TEST_F (TestTestCases, DISABLED_nextautomata1)
{
  run_test_case_test ("nextautomata1", ".btor", "nextautomata1");
}

TEST_F (TestTestCases, DISABLED_nextautomata2)
{
  run_test_case_test ("nextautomata2", ".btor", "nextautomata2");
}

TEST_F (TestTestCases, DISABLED_nextautomata3)
{
  run_test_case_test ("nextautomata3", ".btor", "nextautomata3");
}

TEST_F (TestTestCases, DISABLED_nextautomata4)
{
  run_test_case_test ("nextautomata4", ".btor", "nextautomata4");
}

TEST_F (TestTestCases, DISABLED_nextarray1)
{
  run_test_case_test ("nextarray1", ".btor", "nextarray1");
}

TEST_F (TestTestCases, DISABLED_nextarray2)
{
  run_test_case_test ("nextarray2", ".btor", "nextarray2");
}

TEST_F (TestTestCases, DISABLED_nextarray3)
{
  run_test_case_test ("nextarray3", ".btor", "nextarray3");
}

TEST_F (TestTestCases, DISABLED_nextarray4)
{
  run_test_case_test ("nextarray4", ".btor", "nextarray4");
}

TEST_F (TestTestCases, DISABLED_nextarray5)
{
  run_test_case_test ("nextarray5", ".btor", "nextarray5");
}

TEST_F (TestTestCases, DISABLED_nextarray6)
{
  run_test_case_test ("nextarray6", ".btor", "nextarray6");
}

TEST_F (TestTestCases, DISABLED_nextarray7)
{
  run_test_case_test ("nextarray7", ".btor", "nextarray7");
}

TEST_F (TestTestCases, DISABLED_nextarray8)
{
  run_test_case_test ("nextarray8", ".btor", "nextarray8");
}

TEST_F (TestTestCases, DISABLED_nextarray8_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("nextarray8", ".btor", "nextarray8");
}

TEST_F (TestTestCases, DISABLED_nextarrayinput1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("nextarrayinput1", ".btor", "nextarrayinput1");
}

TEST_F (TestTestCases, regpicoprepsqrt4)
{
  run_test_case_test ("regpicoprepsqrt4", ".btor", "regpicoprepsqrt4");
}

TEST_F (TestTestCases, substcyclic1)
{
  run_test_case_test ("substcyclic1", ".btor", "substcyclic1");
}

TEST_F (TestTestCases, lin0) { run_test_case_test ("lin0", ".btor", "lin0"); }

TEST_F (TestTestCases, lin1) { run_test_case_test ("lin1", ".btor", "lin1"); }

TEST_F (TestTestCases, lin2) { run_test_case_test ("lin2", ".btor", "lin2"); }

TEST_F (TestTestCases, lin3) { run_test_case_test ("lin3", ".btor", "lin3"); }

TEST_F (TestTestCases, lin4) { run_test_case_test ("lin4", ".btor", "lin4"); }

TEST_F (TestTestCases, twocomplementassub)
{
  run_test_case_test ("twocomplementassub", ".btor", "twocomplementassub");
}

TEST_F (TestTestCases, regsubslapd149921red)
{
  run_test_case_test ("regsubslapd149921red", ".btor", "regsubslapd149921red");
}

TEST_F (TestTestCases, inc_rwl0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("inc_rwl0", ".btor", "inc_rwl0");
}

TEST_F (TestTestCases, inc_rwl3)
{
  run_test_case_test ("inc_rwl3", ".btor", "inc_rwl3");
}

TEST_F (TestTestCases, dec_rwl0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("dec_rwl0", ".btor", "dec_rwl0");
}

TEST_F (TestTestCases, dec_rwl3)
{
  run_test_case_test ("dec_rwl3", ".btor", "dec_rwl3");
}

TEST_F (TestTestCases, regrembeddedconstraint1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint1", ".btor", "regrembeddedconstraint1");
}

TEST_F (TestTestCases, regrembeddedconstraint1_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint1", ".btor", "regrembeddedconstraint1");
}

TEST_F (TestTestCases, regrembeddedconstraint1_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint1", ".btor", "regrembeddedconstraint1");
}

TEST_F (TestTestCases, regrembeddedconstraint1_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint1", ".btor", "regrembeddedconstraint1");
}

TEST_F (TestTestCases, regrembeddedconstraint2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint2", ".btor", "regrembeddedconstraint2");
}

TEST_F (TestTestCases, regrembeddedconstraint2_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint2", ".btor", "regrembeddedconstraint2");
}

TEST_F (TestTestCases, regrembeddedconstraint2_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint2", ".btor", "regrembeddedconstraint2");
}

TEST_F (TestTestCases, regrembeddedconstraint2_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint2", ".btor", "regrembeddedconstraint2");
}

TEST_F (TestTestCases, regrembeddedconstraint3_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint3", ".btor", "regrembeddedconstraint3");
}

TEST_F (TestTestCases, regrembeddedconstraint3_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint3", ".btor", "regrembeddedconstraint3");
}

TEST_F (TestTestCases, regrembeddedconstraint3_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint3", ".btor", "regrembeddedconstraint3");
}

TEST_F (TestTestCases, regrembeddedconstraint3_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint3", ".btor", "regrembeddedconstraint3");
}

TEST_F (TestTestCases, regrembeddedconstraint4_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint4", ".btor", "regrembeddedconstraint4");
}

TEST_F (TestTestCases, regrembeddedconstraint4_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint4", ".btor", "regrembeddedconstraint4");
}

TEST_F (TestTestCases, regrembeddedconstraint4_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint4", ".btor", "regrembeddedconstraint4");
}

TEST_F (TestTestCases, regrembeddedconstraint4_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint4", ".btor", "regrembeddedconstraint4");
}

TEST_F (TestTestCases, regrembeddedconstraint5_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint5", ".btor", "regrembeddedconstraint5");
}

TEST_F (TestTestCases, regrembeddedconstraint5_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint5", ".btor", "regrembeddedconstraint5");
}

TEST_F (TestTestCases, regrembeddedconstraint5_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint5", ".btor", "regrembeddedconstraint5");
}

TEST_F (TestTestCases, regrembeddedconstraint5_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint5", ".btor", "regrembeddedconstraint5");
}

TEST_F (TestTestCases, regrembeddedconstraint6_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint6", ".btor", "regrembeddedconstraint6");
}

TEST_F (TestTestCases, regrembeddedconstraint6_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint6", ".btor", "regrembeddedconstraint6");
}

TEST_F (TestTestCases, regrembeddedconstraint6_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint6", ".btor", "regrembeddedconstraint6");
}

TEST_F (TestTestCases, regrembeddedconstraint6_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint6", ".btor", "regrembeddedconstraint6");
}

TEST_F (TestTestCases, regrembeddedconstraint7_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint7", ".btor", "regrembeddedconstraint7");
}

TEST_F (TestTestCases, regrembeddedconstraint7_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint7", ".btor", "regrembeddedconstraint7");
}

TEST_F (TestTestCases, regrembeddedconstraint7_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint7", ".btor", "regrembeddedconstraint7");
}

TEST_F (TestTestCases, regrembeddedconstraint7_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint7", ".btor", "regrembeddedconstraint7");
}

TEST_F (TestTestCases, regrembeddedconstraint8_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint8", ".btor", "regrembeddedconstraint8");
}

TEST_F (TestTestCases, regrembeddedconstraint8_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint8", ".btor", "regrembeddedconstraint8");
}

TEST_F (TestTestCases, regrembeddedconstraint8_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint8", ".btor", "regrembeddedconstraint8");
}

TEST_F (TestTestCases, regrembeddedconstraint8_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint8", ".btor", "regrembeddedconstraint8");
}

TEST_F (TestTestCases, regrembeddedconstraint9_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint9", ".btor", "regrembeddedconstraint9");
}

TEST_F (TestTestCases, regrembeddedconstraint9_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint9", ".btor", "regrembeddedconstraint9");
}

TEST_F (TestTestCases, regrembeddedconstraint9_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint9", ".btor", "regrembeddedconstraint9");
}

TEST_F (TestTestCases, regrembeddedconstraint9_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint9", ".btor", "regrembeddedconstraint9");
}

TEST_F (TestTestCases, regrembeddedconstraint10_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint10", ".btor", "regrembeddedconstraint10");
}

TEST_F (TestTestCases, regrembeddedconstraint10_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint10", ".btor", "regrembeddedconstraint10");
}

TEST_F (TestTestCases, regrembeddedconstraint10_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint10", ".btor", "regrembeddedconstraint10");
}

TEST_F (TestTestCases, regrembeddedconstraint10_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint10", ".btor", "regrembeddedconstraint10");
}

TEST_F (TestTestCases, regrembeddedconstraint11_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint11", ".btor", "regrembeddedconstraint11");
}

TEST_F (TestTestCases, regrembeddedconstraint11_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint11", ".btor", "regrembeddedconstraint11");
}

TEST_F (TestTestCases, regrembeddedconstraint11_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint11", ".btor", "regrembeddedconstraint11");
}

TEST_F (TestTestCases, regrembeddedconstraint11_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint11", ".btor", "regrembeddedconstraint11");
}

TEST_F (TestTestCases, regrembeddedconstraint12_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint12", ".btor", "regrembeddedconstraint12");
}

TEST_F (TestTestCases, regrembeddedconstraint12_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint12", ".btor", "regrembeddedconstraint12");
}

TEST_F (TestTestCases, regrembeddedconstraint12_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint12", ".btor", "regrembeddedconstraint12");
}

TEST_F (TestTestCases, regrembeddedconstraint12_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint12", ".btor", "regrembeddedconstraint12");
}

TEST_F (TestTestCases, regrembeddedconstraint13_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint13", ".btor", "regrembeddedconstraint13");
}

TEST_F (TestTestCases, regrembeddedconstraint13_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint13", ".btor", "regrembeddedconstraint13");
}

TEST_F (TestTestCases, regrembeddedconstraint13_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint13", ".btor", "regrembeddedconstraint13");
}

TEST_F (TestTestCases, regrembeddedconstraint13_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint13", ".btor", "regrembeddedconstraint13");
}

TEST_F (TestTestCases, regrembeddedconstraint14_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test (
      "regrembeddedconstraint14", ".btor", "regrembeddedconstraint14");
}

TEST_F (TestTestCases, regrembeddedconstraint14_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test (
      "regrembeddedconstraint14", ".btor", "regrembeddedconstraint14");
}

TEST_F (TestTestCases, regrembeddedconstraint14_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test (
      "regrembeddedconstraint14", ".btor", "regrembeddedconstraint14");
}

TEST_F (TestTestCases, regrembeddedconstraint14_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test (
      "regrembeddedconstraint14", ".btor", "regrembeddedconstraint14");
}

TEST_F (TestTestCases, regrbfs1_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regrbfs1", ".btor", "regrbfs1");
}

TEST_F (TestTestCases, regrbfs1_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regrbfs1", ".btor", "regrbfs1");
}

TEST_F (TestTestCases, regrbfs1_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regrbfs1", ".btor", "regrbfs1");
}

TEST_F (TestTestCases, regrbfs1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regrbfs1", ".btor", "regrbfs1");
}

TEST_F (TestTestCases, regrmark1_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regrmark1", ".btor", "regrmark1");
}

TEST_F (TestTestCases, regrmark1_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regrmark1", ".btor", "regrmark1");
}

TEST_F (TestTestCases, regrmark1_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regrmark1", ".btor", "regrmark1");
}

TEST_F (TestTestCases, regrmark1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regrmark1", ".btor", "regrmark1");
}

TEST_F (TestTestCases, regrmark2_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regrmark2", ".btor", "regrmark2");
}

TEST_F (TestTestCases, regrmark2_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regrmark2", ".btor", "regrmark2");
}

TEST_F (TestTestCases, regrmark2_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regrmark2", ".btor", "regrmark2");
}

TEST_F (TestTestCases, regrmark2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regrmark2", ".btor", "regrmark2");
}

TEST_F (TestTestCases, regrmark3_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regrmark3", ".btor", "regrmark3");
}

TEST_F (TestTestCases, regrmark3_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regrmark3", ".btor", "regrmark3");
}

TEST_F (TestTestCases, regrmark3_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regrmark3", ".btor", "regrmark3");
}

TEST_F (TestTestCases, regrmark3_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regrmark3", ".btor", "regrmark3");
}

TEST_F (TestTestCases, regr3vl1_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regr3vl1", ".btor", "regr3vl1");
}

TEST_F (TestTestCases, regr3vl1_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regr3vl1", ".btor", "regr3vl1");
}

TEST_F (TestTestCases, regr3vl1_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regr3vl1", ".btor", "regr3vl1");
}

TEST_F (TestTestCases, regr3vl1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regr3vl1", ".btor", "regr3vl1");
}

TEST_F (TestTestCases, regr3vl2_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regr3vl2", ".btor", "regr3vl2");
}

TEST_F (TestTestCases, regr3vl2_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regr3vl2", ".btor", "regr3vl2");
}

TEST_F (TestTestCases, regr3vl2_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regr3vl2", ".btor", "regr3vl2");
}

TEST_F (TestTestCases, regr3vl2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regr3vl2", ".btor", "regr3vl2");
}

TEST_F (TestTestCases, regr3vl3_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regr3vl3", ".btor", "regr3vl3");
}

TEST_F (TestTestCases, regr3vl3_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regr3vl3", ".btor", "regr3vl3");
}

TEST_F (TestTestCases, regr3vl3_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regr3vl3", ".btor", "regr3vl3");
}

TEST_F (TestTestCases, regr3vl3_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regr3vl3", ".btor", "regr3vl3");
}

TEST_F (TestTestCases, regr3vl4_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regr3vl4", ".btor", "regr3vl4");
}

TEST_F (TestTestCases, regr3vl4_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regr3vl4", ".btor", "regr3vl4");
}

TEST_F (TestTestCases, regr3vl4_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regr3vl4", ".btor", "regr3vl4");
}

TEST_F (TestTestCases, regr3vl4_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regr3vl4", ".btor", "regr3vl4");
}

TEST_F (TestTestCases, regrexpleak1_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regrexpleak1", ".btor", "regrexpleak1");
}

TEST_F (TestTestCases, regrexpleak1_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regrexpleak1", ".btor", "regrexpleak1");
}

TEST_F (TestTestCases, regrexpleak1_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regrexpleak1", ".btor", "regrexpleak1");
}

TEST_F (TestTestCases, regrexpleak1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regrexpleak1", ".btor", "regrexpleak1");
}

TEST_F (TestTestCases, regrexpleak2_3)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 3);
  run_test_case_test ("regrexpleak2", ".btor", "regrexpleak2");
}

TEST_F (TestTestCases, regrexpleak2_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("regrexpleak2", ".btor", "regrexpleak2");
}

TEST_F (TestTestCases, regrexpleak2_1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regrexpleak2", ".btor", "regrexpleak2");
}

TEST_F (TestTestCases, regrexpleak2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("regrexpleak2", ".btor", "regrexpleak2");
}

TEST_F (TestTestCases, regrpointerchasing1)
{
  run_test_case_test ("regrpointerchasing1", ".btor", "regrpointerchasing1");
}

TEST_F (TestTestCases, 3vl1_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("3vl1", ".btor", "3vl1");
}

TEST_F (TestTestCases, 3vl1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("3vl1", ".btor", "3vl1");
}

TEST_F (TestTestCases, 3vl2_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("3vl2", ".btor", "3vl2");
}

TEST_F (TestTestCases, 3vl2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("3vl2", ".btor", "3vl2");
}

TEST_F (TestTestCases, 3vl3_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("3vl3", ".btor", "3vl3");
}

TEST_F (TestTestCases, 3vl3_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("3vl3", ".btor", "3vl3");
}

TEST_F (TestTestCases, 3vl4_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("3vl4", ".btor", "3vl4");
}

TEST_F (TestTestCases, 3vl4_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("3vl4", ".btor", "3vl4");
}

TEST_F (TestTestCases, 3vl5_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("3vl5", ".btor", "3vl5");
}

TEST_F (TestTestCases, 3vl5_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("3vl5", ".btor", "3vl5");
}

TEST_F (TestTestCases, 3vl6_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("3vl6", ".btor", "3vl6");
}

TEST_F (TestTestCases, 3vl6_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("3vl6", ".btor", "3vl6");
}

TEST_F (TestTestCases, udivtheorem1)
{
  run_test_case_test ("udivtheorem1", ".btor", "udivtheorem1");
}

TEST_F (TestTestCases, uremtheorem1)
{
  run_test_case_test ("uremtheorem1", ".btor", "uremtheorem1");
}

TEST_F (TestTestCases, ulttheorem1)
{
  run_test_case_test ("ulttheorem1", ".btor", "ulttheorem1");
}

TEST_F (TestTestCases, ultsubst1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst1", ".btor", "ultsubst1");
}

TEST_F (TestTestCases, ultsubst1_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst1", ".btor", "ultsubst1");
}

TEST_F (TestTestCases, ultsubst2_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst2", ".btor", "ultsubst2");
}

TEST_F (TestTestCases, ultsubst2_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst2", ".btor", "ultsubst2");
}

TEST_F (TestTestCases, ultsubst3_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst3", ".btor", "ultsubst3");
}

TEST_F (TestTestCases, ultsubst3_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst3", ".btor", "ultsubst3");
}

TEST_F (TestTestCases, ultsubst4_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst4", ".btor", "ultsubst4");
}

TEST_F (TestTestCases, ultsubst4_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst4", ".btor", "ultsubst4");
}

TEST_F (TestTestCases, ultsubst5_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst5", ".btor", "ultsubst5");
}

TEST_F (TestTestCases, ultsubst5_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst5", ".btor", "ultsubst5");
}

TEST_F (TestTestCases, ultsubst6_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst6", ".btor", "ultsubst6");
}

TEST_F (TestTestCases, ultsubst6_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst6", ".btor", "ultsubst6");
}

TEST_F (TestTestCases, ultsubst7_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst7", ".btor", "ultsubst7");
}

TEST_F (TestTestCases, ultsubst7_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst7", ".btor", "ultsubst7");
}

TEST_F (TestTestCases, ultsubst8_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst8", ".btor", "ultsubst8");
}

TEST_F (TestTestCases, ultsubst8_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst8", ".btor", "ultsubst8");
}

TEST_F (TestTestCases, ultsubst9_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("ultsubst9", ".btor", "ultsubst9");
}

TEST_F (TestTestCases, ultsubst9_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("ultsubst9", ".btor", "ultsubst9");
}

TEST_F (TestTestCases, slicesubst1_0)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 0);
  run_test_case_test ("slicesubst1", ".btor", "slicesubst1");
}

TEST_F (TestTestCases, slicesubst1_2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("slicesubst1", ".btor", "slicesubst1");
}

TEST_F (TestTestCases, regrdomabst1)
{
  run_test_case_test ("regrdomabst1", ".btor", "regrdomabst1");
}

TEST_F (TestTestCases, regrdomabst2)
{
  run_test_case_test ("regrdomabst2", ".btor", "regrdomabst2");
}

TEST_F (TestTestCases, regrdomabst3)
{
  run_test_case_test ("regrdomabst3", ".btor", "regrdomabst3");
}

TEST_F (TestTestCases, regrdomabst4)
{
  run_test_case_test ("regrdomabst4", ".btor", "regrdomabst4");
}

TEST_F (TestTestCases, problem_130)
{
  run_test_case_test ("problem_130", ".smt2", "problem_130");
}

TEST_F (TestTestCases, distri1)
{
  run_test_case_test ("distri1", ".btor", "distri1");
}

TEST_F (TestTestCases, distri2)
{
  run_test_case_test ("distri2", ".btor", "distri2");
}

TEST_F (TestTestCases, distri3)
{
  run_test_case_test ("distri3", ".btor", "distri3");
}

TEST_F (TestTestCases, distri4)
{
  run_test_case_test ("distri4", ".btor", "distri4");
}

TEST_F (TestTestCases, distri5)
{
  run_test_case_test ("distri5", ".btor", "distri5");
}

TEST_F (TestTestCases, distri6)
{
  run_test_case_test ("distri6", ".btor", "distri6");
}

TEST_F (TestTestCases, distri7)
{
  run_test_case_test ("distri7", ".btor", "distri7");
}

TEST_F (TestTestCases, distri8)
{
  run_test_case_test ("distri8", ".btor", "distri8");
}

TEST_F (TestTestCases, redor3)
{
  run_test_case_test ("redor3", ".btor", "redor3");
}

TEST_F (TestTestCases, redand3twice)
{
  run_test_case_test ("redand3twice", ".btor", "redand3twice");
}

TEST_F (TestTestCases, painc)
{
  boolector_set_opt (d_btor, BTOR_OPT_INCREMENTAL, 1);
  run_test_case_test ("painc", ".smt2", "painc");
}

TEST_F (TestTestCases, sult) { run_test_case_test ("sult", ".btor", "sult"); }

TEST_F (TestTestCases, sult2)
{
  run_test_case_test ("sult2", ".btor", "sult2");
}

TEST_F (TestTestCases, concatslice1)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test ("concatslice1", ".btor", "concatslice1");
}

TEST_F (TestTestCases, concatslice2)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test ("concatslice2", ".btor", "concatslice2");
}

TEST_F (TestTestCases, regaddnorm1)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test ("regaddnorm1", ".btor", "regaddnorm1");
}

TEST_F (TestTestCases, regaddnorm2)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test ("regaddnorm2", ".btor", "regaddnorm2");
}

TEST_F (TestTestCases, regnegadd1)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test ("regnegadd1", ".btor", "regnegadd1");
}

TEST_F (TestTestCases, sc12fuzzcheck2)
{
  run_test_case_test ("sc12fuzzcheck2", ".smt2", "sc12fuzzcheck2");
}

TEST_F (TestTestCases, regmismatch)
{
  d_expect_parse_error = true;
  run_test_case_test ("regmismatch", ".smt2", "regmismatch");
}

TEST_F (TestTestCases, regrbetacache1)
{
  boolector_set_opt (d_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
  run_test_case_test ("regrbetacache1", ".btor", "regrbetacache1");
}

// !! currently broken since we don't allow to mix lambdas with arrays
TEST_F (TestTestCases, DISABLED_regrbetacache2)
{
  boolector_set_opt (d_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
  run_test_case_test ("regrbetacache2", ".btor", "regrbetacache2");
}

TEST_F (TestTestCases, regrencparamapps)
{
  run_test_case_test ("regrencparamapps", ".smt2", "regrencparamapps");
}

TEST_F (TestTestCases, nestedfun1)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("nestedfun1", ".smt2", "nestedfun1");
}

TEST_F (TestTestCases, regrcollectprem)
{
  run_test_case_test ("regrcollectprem", ".btor", "regrcollectprem");
}

TEST_F (TestTestCases, regrlemmaloop_embeddedconstraints)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 1);
  run_test_case_test ("regrlemmaloop_embeddedconstraints",
                      ".btor",
                      "regrlemmaloop_embeddedconstraints");
}

TEST_F (TestTestCases, addnegmul1)
{
  run_test_case_test ("addnegmul1", ".btor", "addnegmul1");
}

TEST_F (TestTestCases, normaddneg0)
{
  run_test_case_test ("normaddneg0", ".btor", "normaddneg0");
}

TEST_F (TestTestCases, normaddneg1)
{
  run_test_case_test ("normaddneg1", ".btor", "normaddneg1");
}

TEST_F (TestTestCases, normaddneg2)
{
  run_test_case_test ("normaddneg2", ".btor", "normaddneg2");
}

TEST_F (TestTestCases, normaddneg3)
{
  run_test_case_test ("normaddneg3", ".btor", "normaddneg3");
}

TEST_F (TestTestCases, exactlyone)
{
  run_test_case_test ("exactlyone", ".btor", "exactlyone");
}

TEST_F (TestTestCases, normalize_add_incomplete)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test (
      "normalize_add_incomplete", ".btor", "normalize_add_incomplete");
}

TEST_F (TestTestCases, normalize_mul_incomplete)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test (
      "normalize_mul_incomplete", ".btor", "normalize_mul_incomplete");
}

TEST_F (TestTestCases, normalize_and_incomplete)
{
  d_check_sat   = false;
  d_dump        = true;
  d_dump_format = "btor";
  run_test_case_test (
      "normalize_and_incomplete", ".btor", "normalize_and_incomplete");
}

TEST_F (TestTestCases, getvalue1)
{
  run_test_case_test ("getvalue1", ".smt2", "getvalue1");
}

TEST_F (TestTestCases, getvalue2)
{
  run_test_case_test ("getvalue2", ".smt2", "getvalue2");
}

TEST_F (TestTestCases, getvalue3)
{
  run_test_case_test ("getvalue3", ".smt2", "getvalue3");
}

TEST_F (TestTestCases, invalidmodel1)
{
  run_test_case_test ("invalidmodel1", ".smt2", "invalidmodel1");
}

TEST_F (TestTestCases, invalidmodel2)
{
  boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, 2);
  run_test_case_test ("invalidmodel2", ".smt2", "invalidmodel2");
}

TEST_F (TestTestCases, invalidmodel3)
{
  run_test_case_test ("invalidmodel3", ".btor", "invalidmodel3");
}

TEST_F (TestTestCases, regr_distinct)
{
  run_test_case_test ("regr-distinct", ".smt2", "regr-distinct");
}

TEST_F (TestTestCases, regsmtparselet)
{
  run_test_case_test ("regsmtparselet", ".smt2", "regsmtparselet");
}

TEST_F (TestTestCases, smt2pushpop0)
{
  boolector_set_opt (d_btor, BTOR_OPT_INCREMENTAL, 1);
  run_test_case_test ("smt2pushpop0", ".smt2", "smt2pushpop0");
}

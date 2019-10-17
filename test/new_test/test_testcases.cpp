/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
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

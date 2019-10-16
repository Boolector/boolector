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

#include <dirent.h>

extern "C" {
#include "boolector.h"
}

class TestParseError : public TestFile
{
 protected:
  void SetUp () override
  {
    d_expect_parse_error = true;
    TestFile::SetUp ();
  }

  bool hasprefix (const char *str, const char *prefix)
  {
    return !strncmp (str, prefix, strlen (prefix));
  }

  bool hassuffix (const char *str, const char *suffix)
  {
    int32_t difflen = strlen (str) - strlen (suffix);
    if (difflen < 0) return 0;
    return !strcmp (str + difflen, suffix);
  }

  void run_smt_parse_error_test (const char *name)
  {
    if (hassuffix(name, ".smt"))
    {
      boolector_set_opt (d_btor, BTOR_OPT_INPUT_FORMAT, BTOR_INPUT_FORMAT_SMT1);
    }
    else
    {
      assert (hassuffix(name, ".smt2"));
      boolector_set_opt (d_btor, BTOR_OPT_INPUT_FORMAT, BTOR_INPUT_FORMAT_SMT2);
    }
    run_test (name, BOOLECTOR_UNKNOWN);
  }

  uint32_t d_smt = 1;
};

TEST_F (TestParseError, smt2perr)
{
  DIR *dir = opendir (BTOR_OUT_DIR);
  struct dirent *de;

  while ((de = readdir (dir)))
  {
    char *name = de->d_name;
    if (strchr (name, '.') != nullptr)
    {
      if ((hasprefix (name, "smt1perr") || hasprefix (name, "smt2perr"))
          && (hassuffix (name, ".smt") || hassuffix (name, ".smt2")))
      {
        run_smt_parse_error_test (name);
        TearDown();
        SetUp();
      }
    }
  }
  closedir (dir);
}

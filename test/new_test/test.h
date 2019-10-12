/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TEST_H_INCLUDED
#define TEST_H_INCLUDED

#include <fstream>
#include <sstream>
#include <string>
#include "gtest/gtest.h"

extern "C" {
#include "btorconfig.h"
#include "btorcore.h"
}

class TestBtor : public ::testing::Test
{
 protected:
  void SetUp () override { btor = btor_new (); }

  void TearDown () override
  {
    if (btor)
    {
      btor_delete (btor);
    }

    if (log_file)
    {
      fclose (log_file);
      check_log_file ();
    }
  }

  void open_log_file (std::string name)
  {
    std::stringstream ss_log, ss_out;
    ss_log << BTOR_LOG_DIR << name << ".log";
    ss_out << BTOR_OUT_DIR << name << ".out";

    log_file_name = ss_log.str ();
    out_file_name = ss_out.str ();
    std::cout << "log_file " << log_file_name << std::endl;
    std::cout << "out_file " << out_file_name << std::endl;
    log_file = fopen (log_file_name.c_str (), "w");
  }

  void check_log_file ()
  {
    std::ifstream log_file (log_file_name,
                            std::ifstream::binary | std::ifstream::ate);
    std::ifstream out_file (out_file_name,
                            std::ifstream::binary | std::ifstream::ate);

    ASSERT_TRUE (!log_file.fail () && !out_file.fail ());

    log_file.seekg (0, std::ifstream::beg);
    out_file.seekg (0, std::ifstream::beg);
    ASSERT_TRUE (
        std::equal (std::istreambuf_iterator<char> (log_file.rdbuf ()),
                    std::istreambuf_iterator<char> (),
                    std::istreambuf_iterator<char> (out_file.rdbuf ())));
  }

  std::string log_file_name;
  std::string out_file_name;
  FILE* log_file = nullptr;
  Btor* btor     = nullptr;
};
#endif

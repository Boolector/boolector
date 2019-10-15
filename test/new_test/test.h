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
#include "boolector.h"
#include "btorconfig.h"
#include "btorcore.h"
}

class TestCommon : public ::testing::Test
{
 protected:
  void TearDown () override
  {
    if (d_log_file)
    {
      fclose (d_log_file);
      d_log_file = nullptr;
      if (d_check_log_file) check_log_file ();
    }
  }

  void open_log_file (std::string name)
  {
    std::stringstream ss_log, ss_out;
    ss_log << BTOR_LOG_DIR << name << ".log";
    ss_out << BTOR_OUT_DIR << name << ".out";

    d_log_file_name = ss_log.str ();
    d_out_file_name = ss_out.str ();
    d_log_file      = fopen (d_log_file_name.c_str (), "w");
  }

  void check_log_file ()
  {
    std::ifstream log_file (d_log_file_name,
                            std::ifstream::binary | std::ifstream::ate);
    std::ifstream out_file (d_out_file_name,
                            std::ifstream::binary | std::ifstream::ate);

    ASSERT_TRUE (!log_file.fail () && !out_file.fail ());

    log_file.seekg (0, std::ifstream::beg);
    out_file.seekg (0, std::ifstream::beg);
    ASSERT_TRUE (
        std::equal (std::istreambuf_iterator<char> (log_file.rdbuf ()),
                    std::istreambuf_iterator<char> (),
                    std::istreambuf_iterator<char> (out_file.rdbuf ())));
  }

  std::string d_log_file_name;
  std::string d_out_file_name;
  FILE* d_log_file = nullptr;
  bool d_check_log_file = true;
};

class TestMm : public TestCommon
{
 protected:
  void SetUp () override { d_mm = btor_mem_mgr_new (); }

  void TearDown () override
  {
    if (d_mm)
    {
      btor_mem_mgr_delete (d_mm);
      d_mm = nullptr;
    }

    TestCommon::TearDown ();
  }

  BtorMemMgr* d_mm = nullptr;
};

class TestBtor : public TestCommon
{
 protected:
  void SetUp () override { d_btor = btor_new (); }

  void TearDown () override
  {
    if (d_btor)
    {
      btor_delete (d_btor);
      d_btor = nullptr;
    }

    TestCommon::TearDown ();
  }

  Btor* d_btor = nullptr;
};

class TestBoolector : public TestCommon
{
 protected:
  void SetUp () override { d_btor = boolector_new (); }

  void TearDown () override
  {
    if (d_btor)
    {
      boolector_delete (d_btor);
    }

    TestCommon::TearDown ();
  }

  Btor* d_btor = nullptr;
};

#endif

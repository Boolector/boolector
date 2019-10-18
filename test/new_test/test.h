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

class TestFile : public TestBoolector
{
 protected:
  void run_test (const char* name,
                 int32_t expected,
                 uint32_t verbosity = 0u)
  {
    if (!d_log_file)
    {
      std::string s(name);
      size_t pos = s.rfind('.');
      assert (pos != std::string::npos);
      std::string base_name = s.substr(0, pos);
      open_log_file (base_name);
    }

    std::stringstream ss_in;
    FILE* f_in;
    int32_t parse_status;
    char* parse_err;
    int32_t sat_res;

    ss_in << BTOR_OUT_DIR << name;
    f_in = fopen (ss_in.str ().c_str (), "r");
    assert (f_in);

    boolector_set_opt (d_btor, BTOR_OPT_VERBOSITY, verbosity);
    boolector_set_opt (d_btor, BTOR_OPT_INCREMENTAL, 1);

    sat_res = boolector_parse (d_btor,
                                 f_in,
                                 ss_in.str ().c_str (),
                                 d_log_file,
                                 &parse_err,
                                 &parse_status);
    if (d_expect_parse_error)
    {
      ASSERT_EQ (sat_res, BOOLECTOR_PARSE_ERROR);
    }
    else
    {
      ASSERT_NE (sat_res, BOOLECTOR_PARSE_ERROR);
    }

    if (d_dump)
    {
      assert (d_log_file);
      if (d_dump_format == "btor")
      {
        boolector_simplify (d_btor);
        boolector_dump_btor (d_btor, d_log_file);
      }
      else
      {
        assert (d_dump_format == "smt2");
        boolector_simplify (d_btor);
        boolector_dump_smt2 (d_btor, d_log_file);
      }
    }

    if (sat_res == BOOLECTOR_PARSE_UNKNOWN)
    {
      sat_res = boolector_sat (d_btor);
      fprintf (d_log_file,
               "%s\n",
               sat_res == BOOLECTOR_SAT
                   ? "sat"
                   : (sat_res == BOOLECTOR_UNSAT ? "unsat" : "unknown"));
    }

    if (d_get_model)
    {
      boolector_print_model (
          d_btor, (char*) d_model_format.c_str (), d_log_file);
    }

    if (expected != BOOLECTOR_UNKNOWN)
    {
      ASSERT_EQ (sat_res, expected);
    }

    fclose (f_in);
  }

  void run_test (const char* name,
                 const char* ext,
                 int32_t expected,
                 uint32_t verbosity = 0u)
  {
    open_log_file (name);
    std::stringstream ss;
    ss << name << ext;
    run_test (ss.str().c_str(), expected, verbosity);
  }

  bool d_expect_parse_error = false;

  bool d_get_model = false;
  std::string d_model_format = "btor";

  bool d_dump               = false;
  std::string d_dump_format = "btor";
};

#endif

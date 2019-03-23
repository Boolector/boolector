/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2018 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTRUNNER_H_INCLUDED
#define TESTRUNNER_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

extern int32_t g_rwreads;
extern FILE *g_logfile;

#define BTOR_RUN_TEST_CHECK_LOG(name) \
  run_test_case (argc, argv, test_##name, #name, true)

#define BTOR_RUN_TEST(name) \
  run_test_case (argc, argv, test_##name, #name, false)

enum BtorTestCaseSpeed
{
  BTOR_FAST_TEST_CASE   = 0,
  BTOR_NORMAL_TEST_CASE = 1,
  BTOR_SLOW_TEST_CASE   = 2,
};

// Break dependencies on 'btorconfig.h' header in 'testrunner.h'.

extern const char *btor_bin_dir;
extern const char *btor_log_dir;
extern const char *btor_contrib_dir;
extern const char *btor_test_dir;

typedef enum BtorTestCaseSpeed BtorTestCaseSpeed;

void init_tests (BtorTestCaseSpeed speed, bool skip_broken);

void print_test_suite_name (const char *name);

void run_boolector (int32_t argc, char **argv);

void run_test_case (int32_t argc,
                    char **argv,
                    void (*funcp) (),
                    char *name,
                    bool check_log_file);

int32_t finish_tests (void);

#endif

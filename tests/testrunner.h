/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012 Aina Niemetz
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTRUNNER_H_INCLUDED
#define TESTRUNNER_H_INCLUDED

#include <stdio.h>
#include "btorconfig.h"

extern int g_rwreads;
extern FILE *g_logfile;

#define BTOR_RUN_TEST_CHECK_LOG(name) \
  run_test_case (argc, argv, test_##name, #name, 1)

#define BTOR_RUN_TEST(name) run_test_case (argc, argv, test_##name, #name, 0)

enum BtorTestCaseSpeed
{
  BTOR_FAST_TEST_CASE   = 0,
  BTOR_NORMAL_TEST_CASE = 1,
  BTOR_SLOW_TEST_CASE   = 2,
};

typedef enum BtorTestCaseSpeed BtorTestCaseSpeed;

void init_tests (BtorTestCaseSpeed speed, int skip_broken);

void print_test_suite_name (const char *name);

void run_test_case (
    int argc, char **argv, void (*funcp) (), char *name, int check_log_file);

void finish_tests (void);

#endif

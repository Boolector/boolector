/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2007-2012 Robert Daniel Brummayer, Armin Biere
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef TESTRUNNER_H_INCLUDED
#define TESTRUNNER_H_INCLUDED

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

void init_tests (BtorTestCaseSpeed speed);

void print_test_suite_name (const char *name);

void run_test_case (
    int argc, char **argv, void (*funcp) (), char *name, int check_log_file);

void finish_tests (void);

#endif

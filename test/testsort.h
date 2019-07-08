/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTSORT_H_INCLUDED
#define TESTSORT_H_INCLUDED

#include <stdint.h>

void init_sort_tests (void);

void run_sort_tests (int32_t argc, char **argv);

void finish_sort_tests (void);

#endif

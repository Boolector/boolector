/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTPROP_H_INCLUDED
#define TESTPROP_H_INCLUDED

#include <stdint.h>

void init_prop_tests (void);

void run_prop_tests (int32_t argc, char **argv);

void finish_prop_tests (void);

#endif

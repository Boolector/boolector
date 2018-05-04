/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTPROPINV_H_INCLUDED
#define TESTPROPINV_H_INCLUDED

#include <stdint.h>

void init_propinv_tests (void);

void run_propinv_tests (int32_t argc, char **argv);

void finish_propinv_tests (void);

#endif

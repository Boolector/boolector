/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTBETAREDUCE_H_INCLUDED
#define TESTBETAREDUCE_H_INCLUDED

#include <stdint.h>

void init_lambda_tests (void);

void run_lambda_tests (int32_t argc, char **argv);

void finish_lambda_tests (void);

#endif

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTCONSTBV_H_INCLUDED
#define TESTCONSTBV_H_INCLUDED

#include <stdint.h>

void init_bitvec_tests (void);

void run_bitvec_tests (int32_t argc, char **argv);

void finish_bitvec_tests (void);

#endif

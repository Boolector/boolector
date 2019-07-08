/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef TESTMC_H_INCLUDED
#define TESTMC_H_INCLUDED

#include <stdint.h>

void init_mc_tests (void);

void run_mc_tests (int32_t argc, char **argv);

void finish_mc_tests (void);

#endif

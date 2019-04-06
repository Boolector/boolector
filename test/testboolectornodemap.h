/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef TESTBOOLECTORNODEMAP_H_INCLUDED
#define TESTBOOLECTORNODEMAP_H_INCLUDED

#include <stdint.h>

void init_boolectornodemap_tests (void);

void run_boolectornodemap_tests (int32_t argc, char **argv);

void finish_boolectornodemap_tests (void);

#endif

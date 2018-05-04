/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTSAT_H_INCLUDED
#define TESTSAT_H_INCLUDED

#include <stdint.h>

void init_sat_tests (void);

void run_sat_tests (int32_t argc, char **argv);

void finish_sat_tests (void);

#endif

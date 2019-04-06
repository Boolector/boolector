/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTSHIFT_H_INCLUDED
#define TESTSHIFT_H_INCLUDED

#include <stdint.h>

void init_shift_tests (void);

void run_shift_tests (int32_t argc, char **argv);

void finish_shift_tests (void);

#endif

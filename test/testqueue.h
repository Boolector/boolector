/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTQUEUE_H_INCLUDED
#define TESTQUEUE_H_INCLUDED

#include <stdint.h>

void init_queue_tests (void);

void run_queue_tests (int32_t argc, char **argv);

void finish_queue_tests (void);

#endif

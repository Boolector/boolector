/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef TESTMAP_H_INCLUDED
#define TESTMAP_H_INCLUDED

#include <stdint.h>

void init_map_tests (void);

void run_map_tests (int32_t argc, char **argv);

void finish_map_tests (void);

#endif

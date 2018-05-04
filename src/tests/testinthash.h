/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTINTHASH_H_INCLUDED
#define TESTINTHASH_H_INCLUDED

#include <stdint.h>

void init_int_hash_table_tests (void);

void run_int_hash_table_tests (int32_t argc, char **argv);

void finish_int_hash_table_tests (void);

#endif

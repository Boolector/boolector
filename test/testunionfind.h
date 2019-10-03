/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTUNIONFIND_H_INCLUDED
#define TESTUNIONFIND_H_INCLUDED

#include <stdint.h>

void init_ufind_tests (void);

void run_ufind_tests (int32_t argc, char **argv);

void finish_ufind_tests (void);

#endif


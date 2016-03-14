/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTPROP_H_INCLUDED
#define TESTPROP_H_INCLUDED

void init_prop_tests (void);

void run_prop_tests (int argc, char **argv);

void finish_prop_tests (void);

#endif

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTLOGIC_H_INCLUDED
#define TESTLOGIC_H_INCLUDED

void init_logic_tests (void);

void run_logic_tests (int argc, char **argv);

void finish_logic_tests (void);

#endif

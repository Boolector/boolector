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

#ifndef TESTMODELGEN_H_INCLUDED
#define TESTMODELGEN_H_INCLUDED

void init_modelgen_tests (void);

void run_modelgen_tests (int argc, char **argv);

void finish_modelgen_tests (void);

#endif

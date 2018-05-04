/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTOREXIT_H_INCLUDED
#define BTOREXIT_H_INCLUDED

enum BtorExitCode
{
  BTOR_SUCC_EXIT    = 0,
  BTOR_ERR_EXIT     = 1,
  BTOR_SAT_EXIT     = 10,
  BTOR_UNSAT_EXIT   = 20,
  BTOR_UNKNOWN_EXIT = 0
};

typedef enum BtorExitCode BtorExitCode;

#endif

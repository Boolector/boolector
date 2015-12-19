/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOREFSOLVER_H_INCLUDED
#define BTOREFSOLVER_H_INCLUDED

#include "btorslv.h"
#include "btortypes.h"
#include "utils/btorhashptr.h"

struct BtorEFSolver
{
  BTOR_SOLVER_STRUCT;

  Btor *exists_solver;
  BtorPtrHashTable *e_exists_vars;
  Btor *forall_solver;
  BtorPtrHashTable *f_exists_vars;
  BtorPtrHashTable *f_forall_vars;

  struct
  {
    uint32_t refinements;
  } stats;
};

typedef struct BtorEFSolver BtorEFSolver;

BtorSolver *btor_new_ef_solver (Btor *btor);

#endif

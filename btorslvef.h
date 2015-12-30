/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLVEF_H_INCLUDED
#define BTORSLVEF_H_INCLUDED

#include "btorslv.h"
#include "btortypes.h"
#include "utils/btorhashptr.h"

#include <stdint.h>

struct BtorEFSolver
{
  BTOR_SOLVER_STRUCT;

  Btor *exists_solver;
  BtorPtrHashTable *e_exists_vars;
  Btor *forall_solver;
  BtorPtrHashTable *f_exists_vars;
  BtorPtrHashTable *f_forall_vars;
  BtorNode *f_formula;

  struct
  {
    uint32_t refinements;
  } stats;

  struct
  {
    double exists_solver;
    double forall_solver;
  } time;
};

typedef struct BtorEFSolver BtorEFSolver;

BtorSolver *btor_new_ef_solver (Btor *btor);

#endif

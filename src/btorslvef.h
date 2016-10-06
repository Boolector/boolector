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
#include "utils/btornodemap.h"

#include <stdint.h>

struct BtorEFStats
{
  struct
  {
    uint32_t refinements;
    uint32_t failed_refinements;
  } stats;

  struct
  {
    double e_solver;
    double f_solver;
    double synth;
    double qinst;
    double findinst;
  } time;
};

typedef struct BtorEFStats BtorEFStats;

struct BtorEFSolver
{
  BTOR_SOLVER_STRUCT;
  BtorEFStats statistics;
  BtorEFStats dual_statistics;
};

typedef struct BtorEFSolver BtorEFSolver;

BtorSolver* btor_new_ef_solver (Btor* btor);

#endif

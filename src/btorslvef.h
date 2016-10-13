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

    /* overall synthesize statistics */
    uint32_t synthesize_const;
    uint32_t synthesize_term;
    uint32_t synthesize_none;

    /* statistics for the currently synthesized model */
    uint32_t synthesize_model_const;
    uint32_t synthesize_model_term;
    uint32_t synthesize_model_none;
  } stats;

  struct
  {
    double e_solver;
    double f_solver;
    double synth;
    double qinst;
    double findpm;
    double checkinst;
  } time;
};

typedef struct BtorEFStats BtorEFStats;

struct BtorEFSolver
{
  BTOR_SOLVER_STRUCT;
  BtorSolverResult solver_result;
  BtorSolverResult dual_solver_result;
  BtorEFStats statistics;
  BtorEFStats dual_statistics;
};

typedef struct BtorEFSolver BtorEFSolver;

BtorSolver* btor_new_ef_solver (Btor* btor);

#endif

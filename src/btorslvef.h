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

struct BtorEFSolver
{
  BTOR_SOLVER_STRUCT;

  struct
  {
    uint32_t refinements;
    uint32_t synth_aborts;
    uint32_t synth_funs;
    uint32_t synth_funs_reused;
  } stats;

  struct
  {
    double e_solver;
    double f_solver;
    double synth;
    double qinst;
    double findinst;

    double dual_e_solver;
    double dual_f_solver;
    double dual_synth;
    double dual_qinst;
    double dual_findinst;
  } time;
};

typedef struct BtorEFSolver BtorEFSolver;

BtorSolver* btor_new_ef_solver (Btor* btor);

#endif

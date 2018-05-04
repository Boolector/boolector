/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORAIGPROP_H_INCLUDED
#define BTORAIGPROP_H_INCLUDED

#include "aigprop.h"
#include "btorslv.h"

#define BTOR_AIGPROP_SOLVER(btor) ((BtorAIGPropSolver *) (btor)->slv)

struct BtorAIGPropSolver
{
  BTOR_SOLVER_STRUCT;

  AIGProp *aprop;

  /* statistics */
  struct
  {
    uint32_t moves;
    uint32_t restarts;
  } stats;
  struct
  {
    double aprop_sat;
    double aprop_update_cone;
    double aprop_update_cone_reset;
    double aprop_update_cone_model_gen;
    double aprop_update_cone_compute_score;
  } time;
};

typedef struct BtorAIGPropSolver BtorAIGPropSolver;

BtorSolver *btor_new_aigprop_solver (Btor *btor);

#endif

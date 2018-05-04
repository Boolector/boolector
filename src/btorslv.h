/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLV_H_INCLUDED
#define BTORSLV_H_INCLUDED

#include "btortypes.h"
#include "utils/btormem.h"
#include "utils/btornodemap.h"

#include <stdbool.h>
#include <stdio.h>

enum BtorSolverKind
{
  BTOR_FUN_SOLVER_KIND,
  BTOR_SLS_SOLVER_KIND,
  BTOR_PROP_SOLVER_KIND,
  BTOR_AIGPROP_SOLVER_KIND,
  BTOR_QUANT_SOLVER_KIND,
};
typedef enum BtorSolverKind BtorSolverKind;

typedef struct BtorSolver *(*BtorSolverClone) (Btor *,
                                               struct BtorSolver *,
                                               BtorNodeMap *);
typedef void (*BtorSolverDelete) (struct BtorSolver *);
typedef BtorSolverResult (*BtorSolverSat) (struct BtorSolver *);
typedef void (*BtorSolverGenerateModel) (struct BtorSolver *, bool, bool);
typedef void (*BtorSolverPrintStats) (struct BtorSolver *);
typedef void (*BtorSolverPrintTimeStats) (struct BtorSolver *);
typedef void (*BtorSolverPrintModel) (struct BtorSolver *,
                                      const char *format,
                                      FILE *file);

#define BTOR_SOLVER_STRUCT                       \
  struct                                         \
  {                                              \
    BtorSolverKind kind;                         \
    Btor *btor;                                  \
    struct                                       \
    {                                            \
      BtorSolverClone clone;                     \
      BtorSolverDelete delet;                    \
      BtorSolverSat sat;                         \
      BtorSolverGenerateModel generate_model;    \
      BtorSolverPrintStats print_stats;          \
      BtorSolverPrintTimeStats print_time_stats; \
      BtorSolverPrintModel print_model;          \
    } api;                                       \
  }

struct BtorSolver
{
  BTOR_SOLVER_STRUCT;
};
typedef struct BtorSolver BtorSolver;

#endif

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLV_H_INCLUDED
#define BTORSLV_H_INCLUDED

#include "btortypes.h"
#include "utils/btormem.h"
#include "utils/btornodemap.h"

enum BtorSolverResult
{
  BTOR_RESULT_SAT     = 10,
  BTOR_RESULT_UNSAT   = 20,
  BTOR_RESULT_UNKNOWN = 0,
};

typedef enum BtorSolverResult BtorSolverResult;

enum BtorSolverKind
{
  BTOR_CORE_SOLVER_KIND,
  BTOR_SLS_SOLVER_KIND,
};
typedef enum BtorSolverKind BtorSolverKind;

typedef struct BtorSolver *(*BtorSolverClone) (Btor *, Btor *, BtorNodeMap *);
typedef void (*BtorSolverDelete) (struct BtorSolver *);
typedef BtorSolverResult (*BtorSolverSat) (struct BtorSolver *);
typedef void (*BtorSolverGenerateModel) (struct BtorSolver *, bool, bool);
typedef void (*BtorSolverPrintStats) (struct BtorSolver *);
typedef void (*BtorSolverPrintTimeStats) (struct BtorSolver *);

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
    } api;                                       \
  }

struct BtorSolver
{
  BTOR_SOLVER_STRUCT;
};
typedef struct BtorSolver BtorSolver;

#endif

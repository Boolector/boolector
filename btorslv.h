/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLV_H_INCLUDED
#define BTORSLV_H_INCLUDED

#include "btortypes.h"
#include "utils/btormap.h"

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
  BTOR_EF_SOLVER_KIND,
};
typedef enum BtorSolverKind BtorSolverKind;

#define BTOR_SOLVER_STRUCT                                         \
  struct                                                           \
  {                                                                \
    BtorSolverKind kind;                                           \
    struct                                                         \
    {                                                              \
      struct BtorSolver *(*clone) (Btor *, Btor *, BtorNodeMap *); \
      void (*delet) (Btor *);                                      \
      BtorSolverResult (*sat) (Btor *);                            \
      void (*generate_model) (Btor *, bool, bool);                 \
      void (*print_stats) (Btor *);                                \
      void (*print_time_stats) (Btor *);                           \
    } api;                                                         \
  }

struct BtorSolver
{
  BTOR_SOLVER_STRUCT;
};
typedef struct BtorSolver BtorSolver;

#endif

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
#include "utils/btormem.h"

enum BtorSolverKind
{
  BTOR_CORE_SOLVER_KIND,
  BTOR_EF_SOLVER_KIND,
};
typedef enum BtorSolverKind BtorSolverKind;

#define BTOR_SOLVER_STRUCT                            \
  struct                                              \
  {                                                   \
    BtorSolverKind kind;                              \
    struct                                            \
    {                                                 \
      void *(*clone) (Btor *, Btor *, BtorNodeMap *); \
      void (*delet) (Btor *);                         \
      int (*sat) (Btor *, int, int);                  \
      void (*generate_model) (Btor *, int, int);      \
      void (*print_stats) (Btor *);                   \
      void (*print_time_stats) (Btor *);              \
    } api;                                            \
  }

struct BtorSolver
{
  BTOR_SOLVER_STRUCT;
};
typedef struct BtorSolver BtorSolver;

#endif

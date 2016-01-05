/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORTYPES_H_INCLUDED
#define BTORTYPES_H_INCLUDED

typedef struct Btor Btor;
typedef struct BtorNode BtorNode;

enum BtorSolverResult
{
  BTOR_RESULT_SAT     = 10,
  BTOR_RESULT_UNSAT   = 20,
  BTOR_RESULT_UNKNOWN = 0,
};

typedef enum BtorSolverResult BtorSolverResult;

/* public API types */
typedef struct BoolectorNode BoolectorNode;
typedef unsigned BoolectorSort;

#endif

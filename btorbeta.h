/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBETA_H_INCLUDED
#define BTORBETA_H_INCLUDED

#include "btorexp.h"

#define BETA_RED_LAMBDA_CHAINS -2
#define BETA_RED_CUTOFF -1
#define BETA_RED_FULL 0
#define BETA_RED_BOUNDED(bound) bound

BtorNode *btor_beta_reduce (Btor *, BtorNode *, int, BtorNode **);

BtorNode *btor_beta_reduce_full (Btor *, BtorNode *);

BtorNode *btor_beta_reduce_chains (Btor *, BtorNode *);

BtorNode *btor_beta_reduce_cutoff (Btor *, BtorNode *, BtorNode **);

BtorNode *btor_beta_reduce_bounded (Btor *, BtorNode *, int);

BtorNode *btor_param_cur_assignment (BtorNode *);

void btor_assign_param (Btor *, BtorNode *, BtorNode *);

void btor_unassign_param (Btor *, BtorNode *);

#endif

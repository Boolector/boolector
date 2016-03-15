/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011-2012 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMINISAT_H_INCLUDED
#define BTORMINISAT_H_INCLUDED

#ifdef BTOR_USE_MINISAT

#include <stdio.h>

#include "btorsat.h"

void *btor_minisat_init (struct BtorSATMgr *);
void btor_minisat_add (struct BtorSATMgr *, int);
int btor_minisat_sat (struct BtorSATMgr *, int);
int btor_minisat_deref (struct BtorSATMgr *, int);
int btor_minisat_repr (struct BtorSATMgr *, int);
void btor_minisat_reset (struct BtorSATMgr *);
void btor_minisat_set_output (struct BtorSATMgr *, FILE *);
void btor_minisat_set_prefix (struct BtorSATMgr *, const char *);
void btor_minisat_enable_verbosity (struct BtorSATMgr *, int);
int btor_minisat_inc_max_var (struct BtorSATMgr *);
int btor_minisat_variables (struct BtorSATMgr *);
void btor_minisat_stats (struct BtorSATMgr *);

void btor_minisat_assume (struct BtorSATMgr *, int);
int btor_minisat_failed (struct BtorSATMgr *, int);
int btor_minisat_fixed (struct BtorSATMgr *, int);
int btor_minisat_changed (struct BtorSATMgr *);
int btor_minisat_inconsistent (struct BtorSATMgr *);

const char *btor_minisat_version (void);

#endif
#endif

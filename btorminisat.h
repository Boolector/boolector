/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011 Armin Biere, FMV, JKU.
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef BTORMINISAT_H_INCLUDED
#define BTORMINISAT_H_INCLUDED

#ifdef BTOR_USE_MINISAT

#include <stdio.h>

#include "btorsat.h"

void *btor_minisat_init (struct BtorSATMgr *);
void btor_minisat_add (struct BtorSATMgr *, int);
int btor_minisat_sat (struct BtorSATMgr *);
int btor_minisat_deref (struct BtorSATMgr *, int);
void btor_minisat_reset (struct BtorSATMgr *);
void btor_minisat_set_output (struct BtorSATMgr *, FILE *);
void btor_minisat_set_prefix (struct BtorSATMgr *, const char *);
void btor_minisat_enable_verbosity (struct BtorSATMgr *);
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

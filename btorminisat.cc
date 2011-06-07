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

#ifdef BTOR_USE_PRECOSAT

#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS
#endif

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

#include "minisat/simp/SimpSolver.h"

extern "C" {

#include "btorminisat.h"
#include "btorsat.h"

void *btor_minisat_init (struct BtorSATMgr *);
int btor_minisat_add (struct BtorSATMgr *, int);
int btor_minisat_sat (struct BtorSATMgr *);
int btor_minisat_deref (struct BtorSATMgr *, int);
void btor_minisat_reset (struct BtorSATMgr *);
void btor_minisat_set_output (struct BtorSATMgr *, FILE *);
void btor_minisat_set_prefix (struct BtorSATMgr *, const char *);
void btor_minisat_enable_verbosity (struct BtorSATMgr *);
int btor_minisat_inc_max_var (struct BtorSATMgr *);
int btor_minisat_variables (struct BtorSATMgr *);
void btor_minisat_stats (struct BtorSATMgr *);

const char *btor_minisat_version (void);
};

#endif

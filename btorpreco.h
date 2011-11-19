/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer, FMV, JKU.
 *  Copyright (C) 2010-2011 Armin Biere, FMV, JKU.
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

#ifndef BTORPRECO_H_INCLUDED
#define BTORPRECO_H_INCLUDED

#ifdef BTOR_USE_PRECOSAT

#include <stdio.h>

struct BtorSATMgr;

void *btor_precosat_init (struct BtorSATMgr *);
void btor_precosat_add (struct BtorSATMgr *, int);
int btor_precosat_sat (struct BtorSATMgr *, int);
int btor_precosat_deref (struct BtorSATMgr *, int);
int btor_precosat_repr (struct BtorSATMgr *, int);
int btor_precosat_fixed (struct BtorSATMgr *, int);
void btor_precosat_reset (struct BtorSATMgr *);
void btor_precosat_set_output (struct BtorSATMgr *, FILE *);
void btor_precosat_set_prefix (struct BtorSATMgr *, const char *);
void btor_precosat_enable_verbosity (struct BtorSATMgr *);
int btor_precosat_inc_max_var (struct BtorSATMgr *);
int btor_precosat_variables (struct BtorSATMgr *);
void btor_precosat_stats (struct BtorSATMgr *);

const char *btor_precosat_version (void);

#endif
#endif

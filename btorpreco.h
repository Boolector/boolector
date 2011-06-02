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
int btor_precosat_add (void *, int);
int btor_precosat_sat (void *);
int btor_precosat_deref (void *, int);
void btor_precosat_reset (void *);
void btor_precosat_set_output (void *, FILE *);
void btor_precosat_set_prefix (void *, const char *);
void btor_precosat_enable_verbosity (void *);
int btor_precosat_inc_max_var (void *);
int btor_precosat_variables (void *);
int btor_precosat_clauses (void *);
void btor_precosat_stats (void *);
int btor_precosat_added_original_clauses (void *);

const char *btor_precosat_version (void);

#endif
#endif

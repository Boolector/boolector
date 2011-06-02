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

void btor_precosat_init ();
int btor_precosat_add (int);
int btor_precosat_sat (int);
int btor_precosat_deref (int);
void btor_precosat_reset ();
void btor_precosat_set_output (FILE *);
void btor_precosat_set_prefix (const char *);
void btor_precosat_enable_verbosity ();
int btor_precosat_inc_max_var ();
int btor_precosat_variables ();
int btor_precosat_clauses ();
void btor_precosat_set_new (void *, void *(*) (void *, size_t));
void btor_precosat_set_delete (void *, void (*) (void *, void *, size_t));
void btor_precosat_set_resize (void *,
                               void *(*) (void *, void *, size_t, size_t));
void btor_precosat_stats (void);
int btor_precosat_added_original_clauses (void);

const char *btor_precosat_version (void);

#endif
#endif

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

#ifndef BTORSAT_H_INCLUDED
#define BTORSAT_H_INCLUDED

#include "btormem.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

typedef struct BtorSATMgr BtorSATMgr;

#define BTOR_UNKNOWN 0
#define BTOR_SAT 10
#define BTOR_UNSAT 20

/* Creates new SAT manager.
 * A SAT manager is used by nearly all functions of the SAT layer.
 */
BtorSATMgr *btor_new_sat_mgr (BtorMemMgr *mm);

BtorMemMgr *btor_mem_mgr_sat (BtorSATMgr *smgr);

/* Sets verbosity [-1,3] */
void btor_set_verbosity_sat_mgr (BtorSATMgr *smgr, int verbosity);

/* Returns if the SAT solver has already been initialized */
int btor_is_initialized_sat (BtorSATMgr *smgr);

/* Deletes SAT manager from memory. */
void btor_delete_sat_mgr (BtorSATMgr *smgr);

/* Generates fresh CNF indices.
 * Indices are generated in consecutive order. */
int btor_next_cnf_id_sat_mgr (BtorSATMgr *smgr);

/* Returns the last CNF index that has been generated. */
int btor_get_last_cnf_id_sat_mgr (BtorSATMgr *smgr);

/* Inits the SAT solver. */
void btor_init_sat (BtorSATMgr *smgr);

/* Sets the output file of the SAT solver. */
void btor_set_output_sat (BtorSATMgr *smgr, FILE *output);

/* Enables verbosity mode of SAT solver. */
void btor_enable_verbosity_sat (BtorSATMgr *smgr);

/* Prints statistics of SAT solver. */
void btor_print_stats_sat (BtorSATMgr *smgr);

/* Adds literal to the current clause of the SAT solver.
 * 0 terminates the current clause.
 */
void btor_add_sat (BtorSATMgr *smgr, int lit);

/* Adds assumption to SAT solver.
 * Requires that SAT solver supports this.
 */
void btor_assume_sat (BtorSATMgr *smgr, int lit);

/* Checks whether an assumption failed during
 * the last SAT solver call 'btor_sat_sat'.
 */
int btor_failed_sat (BtorSATMgr *smgr, int lit);

/* Solves the SAT instance. */
int btor_sat_sat (BtorSATMgr *smgr);

/* Gets assignment of a literal (in the SAT case).
 * Do not call before calling btor_sat_sat.
 */
int btor_deref_sat (BtorSATMgr *smgr, int lit);

/* Resets the status of the SAT solver. */
void btor_reset_sat (BtorSATMgr *smgr);

/* Determines if assignments have been changed
 * as constraints have been added.
 */
int btor_changed_sat (BtorSATMgr *smgr);

#ifdef BTOR_USE_LINGELING
/* Enables Lingeling as SAT preprocessor. */
void btor_enable_lingeling_sat (BtorSATMgr *smgr);
#endif

#ifdef BTOR_USE_PRECOSAT
/* Enables PrecoSAT as SAT preprocessor. */
void btor_enable_precosat_sat (BtorSATMgr *smgr);
#endif

/* Only used for debugging purposes */
int btor_incremental_sat (BtorSATMgr *smgr);

#endif

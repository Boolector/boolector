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
BtorSATMgr *btor_new_sat_mgr (BtorMemMgr *mm, int verbosity);

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

/* Dumps the CNF of the SAT solver to file. */
void btor_dump_cnf_sat (BtorSATMgr *smgr, FILE *output);

/* Adds assumption to SAT solver. */
void btor_assume_sat (BtorSATMgr *smgr, int lit);

/* Solves the SAT instance. */
int btor_sat_sat (BtorSATMgr *smgr, int limit);

/* Gets assignment of a literal (in the SAT case).
 * Do not call before calling btor_sat_sat.
 */
int btor_deref_sat (BtorSATMgr *smgr, int lit);

/* Resets the status of the SAT solver. */
void btor_reset_sat (BtorSATMgr *smgr);

#endif

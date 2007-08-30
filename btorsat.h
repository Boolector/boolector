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

BtorSATMgr *btor_new_sat_mgr (BtorMemMgr *mm, int verbosity);

int btor_next_cnf_id_sat_mgr (BtorSATMgr *smgr);

void btor_delete_sat_mgr (BtorSATMgr *smgr);

void btor_init_sat (BtorSATMgr *smgr);

void btor_set_output_sat (BtorSATMgr *smgr, FILE *output);

void btor_enable_verbosity_sat (BtorSATMgr *smgr);

void btor_print_stats_sat (BtorSATMgr *smgr);

void btor_add_sat (BtorSATMgr *smgr, int lit);

void btor_dump_cnf_sat (BtorSATMgr *smgr, FILE *output);

void btor_assume_sat (BtorSATMgr *smgr, int lit);

int btor_sat_sat (BtorSATMgr *smgr, int limit);

int btor_deref_sat (BtorSATMgr *smgr, int lit);

void btor_reset_sat (BtorSATMgr *smgr);

#endif

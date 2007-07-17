#ifndef BTORSAT_H_INCLUDED
#define BTORSAT_H_INCLUDED

#include "btormem.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

typedef struct BtorCNFMgr BtorCNFMgr;

#define BTOR_SAT 10
#define BTOR_UNSAT 20

BtorCNFMgr *btor_new_cnf_mgr (BtorMemMgr *mm);

int btor_next_cnf_id_cnf_mgr (BtorCNFMgr *cmgr);

void btor_delete_cnf_mgr (BtorCNFMgr *mgr);

void btor_init_sat (void);

void btor_add_sat (int lit);

void btor_dump_cnf_sat (FILE *output);

void btor_assume_sat (int lit);

int btor_sat_sat (int limit);

int btor_deref_sat (int lit);

void btor_reset_sat (void);

#endif

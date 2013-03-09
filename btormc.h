/*------------------------------------------------------------------------*/

#ifndef btormc_h_INCLUDED
#define btormc_h_INCLUDED

/*------------------------------------------------------------------------*/

#include "boolector.h"

/*------------------------------------------------------------------------*/

typedef struct BtorMC BtorMC;

/*------------------------------------------------------------------------*/

BtorMC *boolector_new_mc (void);
void boolector_set_verbosity_mc (BtorMC *, int verbosity);
void boolector_delete_mc (BtorMC *);

/*------------------------------------------------------------------------*/

BtorNode *boolector_input (BtorMC *, int width, const char *);
BtorNode *boolector_latch (BtorMC *, int width, const char *);
void boolector_next (BtorMC *, BtorNode *latch, BtorNode *next);
void boolector_init (BtorMC *, BtorNode *latch, BtorNode *init);
int boolector_bad (BtorMC *, BtorNode *bad);

/*------------------------------------------------------------------------*/

BtorNode *boolector_time_shift (BtorMC *mc, BtorNode *, int time);
Btor *boolector_mc_btor (BtorMC *mc);

/*------------------------------------------------------------------------*/

int boolector_bmc (BtorMC *, int maxk);

/*------------------------------------------------------------------------*/
#endif

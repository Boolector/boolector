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

int boolector_bmc (BtorMC *, int maxk);

char *boolector_mc_assignment (BtorMC *, BtorNode *input_or_latch, int time);

void boolector_free_mc_assignment (BtorMC *, char *);

/*------------------------------------------------------------------------*/
#endif

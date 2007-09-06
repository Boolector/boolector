#ifndef BTORAIG_H_INCLUDED
#define BTORAIG_H_INCLUDED

#include "btormem.h"
#include "btorsat.h"
#include "btorstack.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

struct BtorAIG
{
  int id;
  struct BtorAIG *children[2];
  int refs;
  int mark;
  int cnf_id;
  struct BtorAIG *next;
};

typedef struct BtorAIG BtorAIG;

#define BTOR_AIG_FALSE ((BtorAIG *) 0ul)
#define BTOR_AIG_TRUE ((BtorAIG *) 1ul)
#define BTOR_IS_CONST_AIG(aig) \
  (((aig) == BTOR_AIG_TRUE) || ((aig) == BTOR_AIG_FALSE))
#define BTOR_INVERT_AIG(aig) ((BtorAIG *) (1ul ^ (unsigned long int) (aig)))
#define BTOR_IS_INVERTED_AIG(aig) (1ul & (unsigned long int) (aig))
#define BTOR_REAL_ADDR_AIG(aig) ((BtorAIG *) (~1ul & (unsigned long int) (aig)))
#define BTOR_IS_VAR_AIG(aig) ((aig)->children[0] == NULL)
#define BTOR_IS_AND_AIG(aig) ((aig)->children[0] != NULL)
#define BTOR_LEFT_CHILD_AIG(aig) ((aig)->children[0])
#define BTOR_RIGHT_CHILD_AIG(aig) ((aig)->children[1])

typedef struct BtorAIGMgr BtorAIGMgr;

BTOR_DECLARE_STACK (AIGPtr, BtorAIG *);

BtorAIGMgr *btor_new_aig_mgr (BtorMemMgr *mm, int verbosity);

void btor_delete_aig_mgr (BtorAIGMgr *amgr);

BtorAIG *btor_var_aig (BtorAIGMgr *amgr);

BtorAIG *btor_not_aig (BtorAIGMgr *amgr, BtorAIG *aig);

BtorAIG *btor_and_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right);

BtorAIG *btor_or_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right);

BtorAIG *btor_eq_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right);

BtorAIG *btor_xor_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right);

BtorAIG *btor_cond_aig (BtorAIGMgr *amgr,
                        BtorAIG *aig_cond,
                        BtorAIG *aig_if,
                        BtorAIG *aig_else);

BtorAIG *btor_copy_aig (BtorAIGMgr *amgr, BtorAIG *aig);

void btor_release_aig (BtorAIGMgr *amgr, BtorAIG *aig);

void btor_dump_aig (BtorAIGMgr *amgr, FILE *output, BtorAIG *aig);

void btor_aig_to_sat (BtorAIGMgr *amgr, BtorAIG *aig);

void btor_mark_aig (BtorAIGMgr *amgr, BtorAIG *aig, int new_mark);

int btor_sat_aig (BtorAIGMgr *amgr, BtorAIG *aig);

BtorSATMgr *btor_get_sat_mgr_aig_mgr (BtorAIGMgr *amgr);

int btor_get_assignment_aig (BtorAIGMgr *amgr, BtorAIG *aig);

#endif

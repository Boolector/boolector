#ifndef BTORAIG_H_INCLUDED
#define BTORAIG_H_INCLUDED

#include "btorhash.h"
#include "btormem.h"
#include "btorsat.h"
#include "btorstack.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

enum BtorCNFEnc
{
  BTOR_TSEITIN_CNF_ENC,
  BTOR_PLAISTED_GREENBAUM_CNF_ENC
};

typedef enum BtorCNFEnc BtorCNFEnc;

struct BtorAIG
{
  int id;
  struct BtorAIG *children[2];
  int refs;
  int cnf_id;
  struct BtorAIG *next;
  unsigned int mark : 2;
  unsigned int pos_imp : 1; /* has positive implication been generated? */
  unsigned int neg_imp : 1; /* has negative implication been generated? */
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
#define BTOR_GET_CNF_ID_AIG(aig)                                  \
  (BTOR_IS_INVERTED_AIG (aig) ? -BTOR_REAL_ADDR_AIG (aig)->cnf_id \
                              : (aig)->cnf_id)

typedef struct BtorAIGMgr BtorAIGMgr;

BTOR_DECLARE_STACK (AIGPtr, BtorAIG *);

/* Creates new AIG manager. An AIG manager is used by nearly all functions
 * of the AIG layer.
 */
BtorAIGMgr *btor_new_aig_mgr (BtorMemMgr *mm, int verbosity);

/* Deletes AIG manager from memory. */
void btor_delete_aig_mgr (BtorAIGMgr *amgr);

/* Variable representing 1 bit. */
BtorAIG *btor_var_aig (BtorAIGMgr *amgr);

/* Inverter. */
BtorAIG *btor_not_aig (BtorAIGMgr *amgr, BtorAIG *aig);

/* Logical AND. */
BtorAIG *btor_and_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right);

/* Logical OR. */
BtorAIG *btor_or_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right);

/* Logical EQUIVALENCE. */
BtorAIG *btor_eq_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right);

/* Logical XOR. */
BtorAIG *btor_xor_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right);

/* If then Else. */
BtorAIG *btor_cond_aig (BtorAIGMgr *amgr,
                        BtorAIG *aig_cond,
                        BtorAIG *aig_if,
                        BtorAIG *aig_else);

/* Copies AIG (increments reference counter). */
BtorAIG *btor_copy_aig (BtorAIGMgr *amgr, BtorAIG *aig);

/* Releases AIG (decrements reference counter).
 * If reference counter reaches 0,
 * then also the children are released
 * and AIG is deleted from memory.
 */
void btor_release_aig (BtorAIGMgr *amgr, BtorAIG *aig);

/* Dumps AIG in AIGER format to file. */
void btor_dump_aig (BtorAIGMgr *amgr, int binary, FILE *output, BtorAIG *aig);

/* Dumps AIGs in AIGER format to file. */
void btor_dump_aigs (BtorAIGMgr *amgr,
                     int binary,
                     FILE *output,
                     BtorAIG **aigs,
                     int naigs,
                     BtorPtrHashTable *back_annotation);

/* Converts AIG into SAT instance. */
void btor_aig_to_sat (BtorAIGMgr *amgr, BtorAIG *aig);

/* Converts AIG fully into SAT instance.
 * This function makes sure that all constraints are fully encoded.
 */
void btor_aig_to_sat_constraints_full (BtorAIGMgr *amgr, BtorAIG *aig);

/* Marks all reachable AIGs with new mark. */
void btor_mark_aig (BtorAIGMgr *amgr, BtorAIG *aig, int new_mark);

/* Solves SAT instance with root AIG aig. */
int btor_sat_aig (BtorAIGMgr *amgr, BtorAIG *aig);

/* Sets CNF encoding strategy. */
void btor_set_cnf_enc_aig_mgr (BtorAIGMgr *amgr, BtorCNFEnc cnf_enc);

/* Gets SAT manager of AIG manager. */
BtorSATMgr *btor_get_sat_mgr_aig_mgr (BtorAIGMgr *amgr);

/* Gets current assignment of AIG aig (in the SAT case).
 * Do not call before calling btor_sat_aig.
 */
int btor_get_assignment_aig (BtorAIGMgr *amgr, BtorAIG *aig);

#endif

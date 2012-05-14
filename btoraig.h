/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer, FMV, JKU
 *  Copyright (C) 2010-2011, Armin Biere, FMV, JKU
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

struct BtorAIG
{
  int id;
  unsigned int refs;
  struct BtorAIG *children[2];
  struct BtorAIG *next;
  int cnf_id;
  unsigned int mark : 2;
  unsigned int local : 30;
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

#define BTOR_GET_CNF_ID_AIG(aig)                                             \
  ((aig) == BTOR_AIG_TRUE                                                    \
       ? 1                                                                   \
       : ((aig) == BTOR_AIG_FALSE ? -1                                       \
                                  : (BTOR_IS_INVERTED_AIG (aig)              \
                                         ? -BTOR_REAL_ADDR_AIG (aig)->cnf_id \
                                         : (aig)->cnf_id)))

typedef struct BtorAIGMgr BtorAIGMgr;

BTOR_DECLARE_STACK (AIGPtr, BtorAIG *);

/* Creates new AIG manager. An AIG manager is used by nearly all functions
 * of the AIG layer.
 */
BtorAIGMgr *btor_new_aig_mgr (BtorMemMgr *mm);

/* Sets verbosity [-1,3] */
void btor_set_verbosity_aig_mgr (BtorAIGMgr *amgr, int verbosity);

/* Gets SAT manager of AIG manager. */
BtorSATMgr *btor_get_sat_mgr_aig_mgr (const BtorAIGMgr *amgr);

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
                     int naigs,
                     BtorAIG **aigs,
                     BtorPtrHashTable *back_annotation);

/* Dumps sequential AIGER model to file. */
void btor_dump_aiger (BtorAIGMgr *amgr,
                      int binary,
                      FILE *output,
                      int naigs,
                      BtorAIG **aigs,
                      int nregs,
                      BtorAIG **regs,
                      BtorAIG **nexts,
                      BtorPtrHashTable *back_annotation);

/* Translates AIG into SAT instance. */
void btor_aig_to_sat (BtorAIGMgr *amgr, BtorAIG *aig);

/* As 'btor_aig_to_sat' but also add the argument as new SAT constraint.
 * Actually this will result in less constraints being generated.
 */
void btor_add_toplevel_aig_to_sat (BtorAIGMgr *, BtorAIG *);

/* Translates AIG into SAT instance in both phases.
 * The function guarantees that after finishing every reachable AIG
 * has a CNF id.
 */
void btor_aig_to_sat_tseitin (BtorAIGMgr *amgr, BtorAIG *aig);

/* Marks all reachable AIGs with new mark. */
void btor_mark_aig (BtorAIGMgr *amgr, BtorAIG *aig, int new_mark);

/* Solves SAT instance with root AIG aig. */
int btor_sat_aig (BtorAIGMgr *amgr, BtorAIG *aig);

/* Gets current assignment of AIG aig (in the SAT case).
 * Do not call before calling btor_sat_aig.
 */
int btor_get_assignment_aig (BtorAIGMgr *amgr, BtorAIG *aig);

#if 0
/* Return a constant aig if the argument aig is fixed to
 * a constant value.  Otherwise return the original argument.
 */
BtorAIG * btor_fixed_aig (BtorAIGMgr * amgr, BtorAIG * aig);
#endif

#endif

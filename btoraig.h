/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORAIG_H_INCLUDED
#define BTORAIG_H_INCLUDED

#include "btorhash.h"
#include "btormem.h"
#include "btorsat.h"
#include "btorstack.h"

#include <stdio.h>

struct BtorAIGMap;

/*------------------------------------------------------------------------*/

struct BtorAIG
{
  int id;
  unsigned int refs;
  struct BtorAIG *children[2];
  struct BtorAIG *next;
  int cnf_id;
  unsigned mark : 2;
  unsigned local;
};

typedef struct BtorAIG BtorAIG;

BTOR_DECLARE_STACK (BtorAIGPtr, BtorAIG *);
BTOR_DECLARE_STACK (BtorAIGPtrPtr, BtorAIG **);

struct BtorAIGUniqueTable
{
  int size;
  int num_elements;
  BtorAIG **chains;
};

typedef struct BtorAIGUniqueTable BtorAIGUniqueTable;

struct BtorAIGMgr
{
  BtorMemMgr *mm;
  BtorMsg *msg;
  BtorAIGUniqueTable table;
  int id;
  int verbosity;
  BtorSATMgr *smgr;
  BtorAIGPtrStack id2aig; /* cnf id to aig */
};

typedef struct BtorAIGMgr BtorAIGMgr;

/*------------------------------------------------------------------------*/

#define BTOR_AIG_FALSE ((BtorAIG *) 0ul)

#define BTOR_AIG_TRUE ((BtorAIG *) 1ul)

#define BTOR_IS_CONST_AIG(aig) \
  (((aig) == BTOR_AIG_TRUE) || ((aig) == BTOR_AIG_FALSE))

#define BTOR_INVERT_AIG(aig) ((BtorAIG *) (1ul ^ (unsigned long int) (aig)))

#define BTOR_IS_INVERTED_AIG(aig) (1ul & (unsigned long int) (aig))

#define BTOR_REAL_ADDR_AIG(aig) ((BtorAIG *) (~1ul & (unsigned long int) (aig)))

#define BTOR_IS_VAR_AIG(aig) (!(aig)->children[0])

#define BTOR_IS_AND_AIG(aig) ((aig)->children[0])

#define BTOR_LEFT_CHILD_AIG(aig) ((aig)->children[0])

#define BTOR_RIGHT_CHILD_AIG(aig) ((aig)->children[1])

#define BTOR_GET_CNF_ID_AIG(aig)                                             \
  ((aig) == BTOR_AIG_TRUE                                                    \
       ? 1                                                                   \
       : ((aig) == BTOR_AIG_FALSE ? -1                                       \
                                  : (BTOR_IS_INVERTED_AIG (aig)              \
                                         ? -BTOR_REAL_ADDR_AIG (aig)->cnf_id \
                                         : (aig)->cnf_id)))

/*------------------------------------------------------------------------*/

/* Creates new AIG manager. An AIG manager is used by nearly all functions
 * of the AIG layer.
 */
BtorAIGMgr *btor_new_aig_mgr (BtorMemMgr *mm, BtorMsg *msg);

/* Clones AIG manager. */
BtorAIGMgr *btor_clone_aig_mgr (BtorMemMgr *mm, BtorMsg *msg, BtorAIGMgr *amgr);

/* Clone all aigs managed by the AIG manager. This needs to be done after
 * cloning the aig manager, as aig_map needs an associated aig manager clone. */
void btor_clone_aigs (BtorAIGMgr *amgr,
                      BtorAIGMgr *clone,
                      struct BtorAIGMap *aig_map);

/* Wrapper to retrieve cloned aigs from aig_map in case that var aigs occur
 * in the aig vector but not as children to non-var aigs. */
BtorAIG *btor_cloned_aig (BtorMemMgr *mm,
                          BtorAIG *aig,
                          struct BtorAIGMap *aig_map);

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

/* Solves SAT instance with root AIG aig. */
int btor_sat_aig (BtorAIGMgr *amgr, BtorAIG *aig);

/* Gets current assignment of AIG aig (in the SAT case).
 * Do not call before calling btor_sat_aig.
 */
int btor_get_assignment_aig (BtorAIGMgr *amgr, BtorAIG *aig);

/* Orders AIGs (actually assume left child of an AND node is smaller
 * than right child
 */
int btor_cmp_aig (BtorAIG *a, BtorAIG *b);

#endif

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORAIG_H_INCLUDED
#define BTORAIG_H_INCLUDED

#include "btoropt.h"
#include "btorsat.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"

#include <stdint.h>
#include <stdio.h>

struct BtorAIGMap;

/*------------------------------------------------------------------------*/

struct BtorAIG
{
  int32_t id;
  int32_t cnf_id;
  uint32_t refs;
  int32_t next; /* next AIG id for unique table */
  uint8_t mark : 2;
  uint8_t is_var : 1; /* is it an AIG variable or an AND? */
  uint32_t local;
  int32_t children[]; /* only allocated for AIG AND */
};

typedef struct BtorAIG BtorAIG;

BTOR_DECLARE_STACK (BtorAIGPtr, BtorAIG *);

struct BtorAIGUniqueTable
{
  int size;
  int num_elements;
  int32_t *chains;
};

typedef struct BtorAIGUniqueTable BtorAIGUniqueTable;

struct BtorAIGMgr
{
  BtorMemMgr *mm;
  BtorMsg *msg;
  BtorOpts *opts;
  BtorAIGUniqueTable table;
  int verbosity;
  BtorSATMgr *smgr;
  BtorAIGPtrStack id2aig; /* id to AIG node */
  BtorIntStack cnfid2aig; /* cnf id to AIG id */

  long long cur_num_aigs;     /* current number of ANDs */
  long long cur_num_aig_vars; /* current number of AIG variables */

  /* statistics */
  long long max_num_aigs;
  long long max_num_aig_vars;
  long long num_cnf_vars;
  long long num_cnf_clauses;
  long long num_cnf_literals;
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

#define BTOR_IS_REGULAR_AIG(aig) (!(1ul & (unsigned long int) (aig)))

#define BTOR_IS_VAR_AIG(aig) ((aig)->is_var)

#define BTOR_IS_AND_AIG(aig) (!(aig)->is_var)

#define BTOR_GET_AIG_BY_ID(amgr, id)                              \
  (id < 0 ? BTOR_INVERT_AIG (BTOR_PEEK_STACK (amgr->id2aig, -id)) \
          : BTOR_PEEK_STACK (amgr->id2aig, id))

#define BTOR_LEFT_CHILD_AIG(amgr, aig) \
  (BTOR_GET_AIG_BY_ID (amgr, (aig)->children[0]))

#define BTOR_RIGHT_CHILD_AIG(amgr, aig) \
  (BTOR_GET_AIG_BY_ID (amgr, (aig)->children[1]))

#define BTOR_GET_ID_AIG(aig) \
  (BTOR_IS_INVERTED_AIG (aig) ? -BTOR_REAL_ADDR_AIG (aig)->id : aig->id)

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
BtorAIGMgr *btor_new_aig_mgr (BtorMemMgr *mm, BtorMsg *msg, BtorOpts *opts);

/* Clones AIG manager. */
BtorAIGMgr *btor_clone_aig_mgr (BtorMemMgr *mm,
                                BtorMsg *msg,
                                BtorOpts *opts,
                                BtorAIGMgr *amgr);

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
int btor_cmp_aig (BtorAIG *aig0, BtorAIG *aig1);

/* hash AIG by id */
unsigned int btor_hash_aig_by_id (BtorAIG *aig);
/* compare AIG by id */
int btor_compare_aig_by_id (BtorAIG *aig0, BtorAIG *aig1);
#endif

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2014-2016 Mathias Preiner.
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
#include "btortypes.h"
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
  uint32_t size;
  uint32_t num_elements;
  int32_t *chains;
};

typedef struct BtorAIGUniqueTable BtorAIGUniqueTable;

struct BtorAIGMgr
{
  Btor *btor;
  BtorAIGUniqueTable table;
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

#define BTOR_INVERT_AIG(aig) ((BtorAIG *) (1ul ^ (unsigned long int) (aig)))

#define BTOR_IS_INVERTED_AIG(aig) (1ul & (unsigned long int) (aig))

#define BTOR_REAL_ADDR_AIG(aig) ((BtorAIG *) (~1ul & (unsigned long int) (aig)))

#define BTOR_IS_REGULAR_AIG(aig) (!(1ul & (unsigned long int) (aig)))

/*------------------------------------------------------------------------*/

static inline bool
btor_aig_is_const (const BtorAIG *aig)
{
  return aig == BTOR_AIG_TRUE || aig == BTOR_AIG_FALSE;
}

static inline bool
btor_aig_is_false (const BtorAIG *aig)
{
  return aig == BTOR_AIG_FALSE;
}

static inline bool
btor_aig_is_true (const BtorAIG *aig)
{
  return aig == BTOR_AIG_TRUE;
}

static inline bool
btor_aig_is_var (const BtorAIG *aig)
{
  if (btor_aig_is_const (aig)) return false;
  return aig->is_var;
}

static inline bool
btor_aig_is_and (const BtorAIG *aig)
{
  if (btor_aig_is_const (aig)) return false;
  return !aig->is_var;
}

static inline int32_t
btor_aig_get_id (const BtorAIG *aig)
{
  assert (aig);
  assert (!btor_aig_is_const (aig));
  return BTOR_IS_INVERTED_AIG (aig) ? -BTOR_REAL_ADDR_AIG (aig)->id : aig->id;
}

static inline BtorAIG *
btor_aig_get_by_id (BtorAIGMgr *amgr, int32_t id)
{
  assert (amgr);

  return id < 0 ? BTOR_INVERT_AIG (BTOR_PEEK_STACK (amgr->id2aig, -id))
                : BTOR_PEEK_STACK (amgr->id2aig, id);
}

static inline int32_t
btor_aig_get_cnf_id (const BtorAIG *aig)
{
  if (btor_aig_is_true (aig)) return 1;
  if (btor_aig_is_false (aig)) return -1;
  return BTOR_IS_INVERTED_AIG (aig) ? -BTOR_REAL_ADDR_AIG (aig)->cnf_id
                                    : aig->cnf_id;
}

static inline BtorAIG *
btor_aig_get_left_child (BtorAIGMgr *amgr, const BtorAIG *aig)
{
  assert (amgr);
  assert (aig);
  assert (!btor_aig_is_const (aig));
  return btor_aig_get_by_id (amgr, BTOR_REAL_ADDR_AIG (aig)->children[0]);
}

static inline BtorAIG *
btor_aig_get_right_child (BtorAIGMgr *amgr, const BtorAIG *aig)
{
  assert (amgr);
  assert (aig);
  assert (!btor_aig_is_const (aig));
  return btor_aig_get_by_id (amgr, BTOR_REAL_ADDR_AIG (aig)->children[1]);
}

/*------------------------------------------------------------------------*/
BtorAIGMgr *btor_new_aig_mgr (Btor *btor);
BtorAIGMgr *btor_clone_aig_mgr (Btor *btor, BtorAIGMgr *amgr);
void btor_delete_aig_mgr (BtorAIGMgr *amgr);

BtorSATMgr *btor_get_sat_mgr_aig_mgr (const BtorAIGMgr *amgr);

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
int btor_compare_aig (const BtorAIG *aig0, const BtorAIG *aig1);

#if 0
/* hash AIG by id */
uint32_t btor_hash_aig_by_id (const BtorAIG * aig);
#endif

/* compare AIG by id */
int btor_compare_aig_by_id (const BtorAIG *aig0, const BtorAIG *aig1);
int btor_compare_aig_by_id_qsort_asc (const void *aig0, const void *aig1);
#endif

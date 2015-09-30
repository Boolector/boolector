/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORAIGVEC_H_INCLUDED
#define BTORAIGVEC_H_INCLUDED

#include "btoraig.h"
#include "btorbitvec.h"
#include "utils/btormem.h"

struct BtorAIGMap;

/*------------------------------------------------------------------------*/

struct BtorAIGVec
{
  uint32_t len; /* length of the AIG vector */
  uint8_t encoded : 1;
  BtorAIG *aigs[]; /* vector of AIGs */
};

typedef struct BtorAIGVec BtorAIGVec;

typedef struct BtorAIGVecMgr BtorAIGVecMgr;

struct BtorAIGVecMgr
{
  BtorMemMgr *mm;
  BtorMsg *msg;
  BtorAIGMgr *amgr;
  long long max_num_aigvecs;
  long long cur_num_aigvecs;
};

/*------------------------------------------------------------------------*/

/* Creates new AIG vector manager. An AIG vector manager is used by nearly
 * all functions of the AIG vector layer.
 */
BtorAIGVecMgr *btor_new_aigvec_mgr (BtorMemMgr *mm, BtorMsg *msg);

/* Clones AIG vector manager. */
BtorAIGVecMgr *btor_clone_aigvec_mgr (BtorMemMgr *mm,
                                      BtorMsg *msg,
                                      BtorAIGVecMgr *avmgr);

/* Returns AIG manager of the AIG vector manager. */
BtorAIGMgr *btor_get_aig_mgr_aigvec_mgr (const BtorAIGVecMgr *avmgr);

/* Deletes AIG vector manager from memory. */
void btor_delete_aigvec_mgr (BtorAIGVecMgr *avmgr);

/* Implicit precondition of all functions taking AIG vectors as inputs:
 * The length of all input AIG vectors have to be greater than zero.
 */

/* Creates new AIG vector representing the constant specified by bits.
 * len(result) = width(bits)
 */
BtorAIGVec *btor_const_aigvec (BtorAIGVecMgr *avmgr, BtorBitVector *bits);

/* Creates new AIG vector representing a variable.
 * len > 0
 * len(result) = len
 */
BtorAIGVec *btor_var_aigvec (BtorAIGVecMgr *avmgr, uint32_t len);

/* Inverts all AIGs of the AIG vector */
void btor_invert_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Creates new AIG vector representing ones's complement of av.
 * len(result) = len(av)
 */
BtorAIGVec *btor_not_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Creates new AIG vector representing a slice of av.
 * upper < len(av)
 * lower >= 0
 * upper >= lower
 * len(result) = upper - lower + 1
 */
BtorAIGVec *btor_slice_aigvec (BtorAIGVecMgr *avmgr,
                               BtorAIGVec *av,
                               uint32_t upper,
                               uint32_t lower);

/* Creates new AIG vector representing av1 AND av2.
 * len(av1) = len(av2)
 * len(result) = len(av1) = len(av2)
 */
BtorAIGVec *btor_and_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 less than av2 (unsigned).
 * len(av1) = len(av2)
 * len(result) = 1
 */
BtorAIGVec *btor_ult_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 equal av2.
 * len(av1) = len(av2)
 * len(result) = 1
 */
BtorAIGVec *btor_eq_aigvec (BtorAIGVecMgr *avmgr,
                            BtorAIGVec *av1,
                            BtorAIGVec *av2);

/* Creates new AIG vector representing av1 + av2.
 * len(av1) = len(av2)
 * len(result) = len(av1) = len(av2)
 */
BtorAIGVec *btor_add_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 shift left logical by av2.
 * is_power_of_2(len(av1))
 * len(av2) = log2(len(av1))
 * len(result) = len(av1)
 */
BtorAIGVec *btor_sll_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);
/* Creates new AIG vector representing av1 shift right logical by av2.
 * is_power_of_2(len(av1))
 * len(av2) = log2(len(av1))
 * len(result) = len(av1)
 */
BtorAIGVec *btor_srl_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 * av2.
 * len(av1) = len(av2)
 * len(result) = len(av1) = len(av2)
 */
BtorAIGVec *btor_mul_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 / av2 (unsigned).
 * len(av1) = len(av2)
 * len(result) = len(av1) = len(av2)
 */
BtorAIGVec *btor_udiv_aigvec (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av1,
                              BtorAIGVec *av2);

/* Creates new AIG vector representing av1 % av2 (unsigned).
 * len(av1) = len(av2)
 * len(result) = len(av1) = len(av2)
 */
BtorAIGVec *btor_urem_aigvec (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av1,
                              BtorAIGVec *av2);

/* Creates new AIG vector representing the concatenation av1.av2.
 * len(result) = len(av1) + len(av2)
 */
BtorAIGVec *btor_concat_aigvec (BtorAIGVecMgr *avmgr,
                                BtorAIGVec *av1,
                                BtorAIGVec *av2);

/* Creates new AIG vector representing av_cond ? av_if : av_else.
 * len(av_cond) = 1
 * len(av_if) = len(av_else)
 * len(result) = len(av_if) = len(av_else)
 */
BtorAIGVec *btor_cond_aigvec (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av_cond,
                              BtorAIGVec *av_if,
                              BtorAIGVec *av_else);

/* Creates new AIG vector representing a copy of av.
 * len(result) = len(av)
 */
BtorAIGVec *btor_copy_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Clones an existing AIG vector. All aigs referenced must already be cloned. */
BtorAIGVec *btor_clone_aigvec (BtorAIGVec *av, BtorAIGVecMgr *avmgr);

/* Translates every AIG of the AIG vector into SAT in both phases  */
void btor_aigvec_to_sat_tseitin (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Release all AIGs of the AIG vector and delete AIG vector from memory. */
void btor_release_delete_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Builds current assignment string of AIG vector (in the SAT case)
 * and returns it.
 */
char *btor_assignment_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

#endif

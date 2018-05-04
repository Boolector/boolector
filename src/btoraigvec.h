/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORAIGVEC_H_INCLUDED
#define BTORAIGVEC_H_INCLUDED

#include "btoraig.h"
#include "btorbv.h"
#include "btoropt.h"
#include "btortypes.h"
#include "utils/btormem.h"

struct BtorAIGMap;

/*------------------------------------------------------------------------*/

struct BtorAIGVec
{
  uint32_t width;  /* width of the AIG vector (cf. bit-width) */
  BtorAIG *aigs[]; /* vector of AIGs */
};

typedef struct BtorAIGVec BtorAIGVec;

typedef struct BtorAIGVecMgr BtorAIGVecMgr;

struct BtorAIGVecMgr
{
  Btor *btor;
  BtorAIGMgr *amgr;
  uint_least64_t max_num_aigvecs;
  uint_least64_t cur_num_aigvecs;
};

/*------------------------------------------------------------------------*/

BtorAIGVecMgr *btor_aigvec_mgr_new (Btor *btor);
BtorAIGVecMgr *btor_aigvec_mgr_clone (Btor *btor, BtorAIGVecMgr *avmgr);
void btor_aigvec_mgr_delete (BtorAIGVecMgr *avmgr);

BtorAIGMgr *btor_aigvec_get_aig_mgr (const BtorAIGVecMgr *avmgr);

/*------------------------------------------------------------------------*/

/* Creates new AIG vector representing the constant specified by bits.
 * width(result) = width(bits)
 */
BtorAIGVec *btor_aigvec_const (BtorAIGVecMgr *avmgr, const BtorBitVector *bits);

/* Creates new AIG vector representing a variable.
 * width > 0
 * width(result) = width
 */
BtorAIGVec *btor_aigvec_var (BtorAIGVecMgr *avmgr, uint32_t width);

/* Inverts all AIGs of the AIG vector */
void btor_aigvec_invert (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Creates new AIG vector representing ones's complement of av.
 * width(result) = width(av)
 */
BtorAIGVec *btor_aigvec_not (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Creates new AIG vector representing a slice of av.
 * upper < width(av)
 * lower >= 0
 * upper >= lower
 * width(result) = upper - lower + 1
 */
BtorAIGVec *btor_aigvec_slice (BtorAIGVecMgr *avmgr,
                               BtorAIGVec *av,
                               uint32_t upper,
                               uint32_t lower);

/* Creates new AIG vector representing av1 AND av2.
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BtorAIGVec *btor_aigvec_and (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 less than av2 (unsigned).
 * width(av1) = width(av2)
 * width(result) = 1
 */
BtorAIGVec *btor_aigvec_ult (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 equal av2.
 * width(av1) = width(av2)
 * width(result) = 1
 */
BtorAIGVec *btor_aigvec_eq (BtorAIGVecMgr *avmgr,
                            BtorAIGVec *av1,
                            BtorAIGVec *av2);

/* Creates new AIG vector representing av1 + av2.
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BtorAIGVec *btor_aigvec_add (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 shift left logical by av2.
 * is_power_of_2(width(av1))
 * width(av2) = log2(width(av1))
 * width(result) = width(av1)
 */
BtorAIGVec *btor_aigvec_sll (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);
/* Creates new AIG vector representing av1 shift right logical by av2.
 * is_power_of_2(width(av1))
 * width(av2) = log2(width(av1))
 * width(result) = width(av1)
 */
BtorAIGVec *btor_aigvec_srl (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 * av2.
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BtorAIGVec *btor_aigvec_mul (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

/* Creates new AIG vector representing av1 / av2 (unsigned).
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BtorAIGVec *btor_aigvec_udiv (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av1,
                              BtorAIGVec *av2);

/* Creates new AIG vector representing av1 % av2 (unsigned).
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BtorAIGVec *btor_aigvec_urem (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av1,
                              BtorAIGVec *av2);

/* Creates new AIG vector representing the concatenation av1.av2.
 * width(result) = width(av1) + width(av2)
 */
BtorAIGVec *btor_aigvec_concat (BtorAIGVecMgr *avmgr,
                                BtorAIGVec *av1,
                                BtorAIGVec *av2);

/* Creates new AIG vector representing av_cond ? av_if : av_else.
 * width(av_cond) = 1
 * width(av_if) = width(av_else)
 * width(result) = width(av_if) = width(av_else)
 */
BtorAIGVec *btor_aigvec_cond (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av_cond,
                              BtorAIGVec *av_if,
                              BtorAIGVec *av_else);

/* Creates new AIG vector representing a copy of av.
 * width(result) = width(av)
 */
BtorAIGVec *btor_aigvec_copy (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Clones an existing AIG vector.
 * All aigs referenced must already be cloned. */
BtorAIGVec *btor_aigvec_clone (BtorAIGVec *av, BtorAIGVecMgr *avmgr);

/* Translates every AIG of the AIG vector into SAT in both phases  */
void btor_aigvec_to_sat_tseitin (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Release all AIGs of the AIG vector and delete AIG vector from memory. */
void btor_aigvec_release_delete (BtorAIGVecMgr *avmgr, BtorAIGVec *av);
#endif

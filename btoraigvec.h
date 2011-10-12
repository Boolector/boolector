/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010  Robert Daniel Brummayer, FMV, JKU
 *  Copyright (C) 2010-2011 Armin Biere, FMV, JKU
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

#ifndef BTORAIGVEC_H_INCLUDED
#define BTORAIGVEC_H_INCLUDED

#include "btoraig.h"
#include "btormem.h"

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

struct BtorAIGVec
{
  BtorAIG **aigs; /* vector of AIGs */
  int len;        /* length of the AIG vector */
};

typedef struct BtorAIGVec BtorAIGVec;

typedef struct BtorAIGVecMgr BtorAIGVecMgr;

/* Creates new AIG vector manager. An AIG vector manager is used by nearly
 * all functions of the AIG vector layer.
 */
BtorAIGVecMgr *btor_new_aigvec_mgr (BtorMemMgr *mm);

/* Sets verbosity [-1,3] */
void btor_set_verbosity_aigvec_mgr (BtorAIGVecMgr *avmgr, int verbosity);

/* Returns AIG manager of the AIG vector manager. */
BtorAIGMgr *btor_get_aig_mgr_aigvec_mgr (const BtorAIGVecMgr *avmgr);

/* Deletes AIG vector manager from memory. */
void btor_delete_aigvec_mgr (BtorAIGVecMgr *avmgr);

/* Implicit precondition of all functions taking AIG vectors as inputs:
 * The length of all input AIG vectors have to be greater than zero.
 */

/* Creates new AIG vector representing a constant specified by bits.
 * len(result) = strlen(bits)
 */
BtorAIGVec *btor_const_aigvec (BtorAIGVecMgr *avmgr, const char *bits);

/* Creates new AIG vector representing a variable.
 * len > 0
 * len(result) = len
 */
BtorAIGVec *btor_var_aigvec (BtorAIGVecMgr *avmgr, int len);

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
                               int upper,
                               int lower);

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

/* Translates every AIG of the AIG vector into SAT in both phases  */
void btor_aigvec_to_sat_tseitin (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Release all AIGs of the AIG vector and delete AIG vector from memory. */
void btor_release_delete_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

/* Builds current assignment string of AIG vector (in the SAT case)
 * and returns it.
 */
char *btor_assignment_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

#endif

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLVPROP_H_INCLUDED
#define BTORSLVPROP_H_INCLUDED

#include "btorbv.h"
#include "btorslv.h"
#include "btortypes.h"
#include "utils/btorhashint.h"

struct BtorPropSolver
{
  BTOR_SOLVER_STRUCT;

  BtorIntHashTable *roots; /* map: maintains 'selected' */
  BtorIntHashTable *score;

  /* current probability for selecting the cond when either the
   * 'then' or 'else' branch is const (path selection) */
  uint32_t flip_cond_const_prob;
  /* current delta for updating the probability for selecting the cond
   * when either the 'then' or 'else' branch is const (path selection) */
  int32_t flip_cond_const_prob_delta;
  /* number of times the cond has already been selected when either
   * the 'then' or 'else' branch is const */
  uint32_t nflip_cond_const;

  struct
  {
    uint32_t restarts;
    uint32_t moves;
    uint32_t rec_conf;
    uint32_t non_rec_conf;
    uint64_t props;
    uint64_t props_cons;
    uint64_t props_inv;
    uint64_t updates;

#ifndef NDEBUG
    uint32_t inv_add;
    uint32_t inv_and;
    uint32_t inv_eq;
    uint32_t inv_ult;
    uint32_t inv_sll;
    uint32_t inv_srl;
    uint32_t inv_mul;
    uint32_t inv_udiv;
    uint32_t inv_urem;
    uint32_t inv_concat;
    uint32_t inv_slice;
    uint32_t inv_cond;

    uint32_t cons_add;
    uint32_t cons_and;
    uint32_t cons_eq;
    uint32_t cons_ult;
    uint32_t cons_sll;
    uint32_t cons_srl;
    uint32_t cons_mul;
    uint32_t cons_udiv;
    uint32_t cons_urem;
    uint32_t cons_concat;
    uint32_t cons_slice;
    uint32_t cons_cond;
#endif
  } stats;

  struct
  {
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
  } time;
};

typedef struct BtorPropSolver BtorPropSolver;

#define BTOR_PROP_SOLVER(btor) ((BtorPropSolver *) (btor)->slv)

BtorSolver *btor_new_prop_solver (Btor *btor);

/*------------------------------------------------------------------------*/

#endif

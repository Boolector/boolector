/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbitvector.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btoriter.h"
#include "btormodel.h"

#define BTOR_SLS_MAXSTEPS_CFACTOR 100  // TODO best value? used by Z3
// TODO best restart scheme? used by Z3
#define BTOR_SLS_MAXSTEPS(i) \
  (BTOR_SLS_MAXSTEPS_CFACTOR * ((i) &1u ? 1 : 1 << ((i) >> 1)))

static int
hamming_distance (BitVector *bv1, BitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int res;
  BitVector *bv, *bvdec = 0, *zero, *ones, *tmp;

  zero = btor_new_bv (btor, bv1->width);
  ones = btor_not_bv (btor, zero);
  bv   = btor_xor_bv (btor, bv1, bv2);
  for (res = 0; !btor_compare_bv (bv, zero); res++)
  {
    bvdec = btor_add_bv (btor, bv, ones);
    tmp   = bv;
    bv    = btor_and_bv (btor, bv, bvdec);
    btor_free_bv (btor, tmp);
  }
  if (bvdec) btor_free_bv (btor, bvdec);
  btor_free_bv (btor, bv);
  btor_free_bv (btor, ones);
  btor_free_bv (btor, zero);
  return res;
}

// score
//
// bw m == 1:
//   s (e[1], A) = A (e[1])
//
// bw m > 1:
//
//   s (e1[m] /\ ... /\ en[m], A) = 1/n * (s (e1[m], A) + ... + s (en[m], A))
//
//   s (e1[m] = e2[m], A)         = (A (e1) == A (e2))
//				    ? 1
//				    : c1 * (1 - (h (A(e1), A(e2)) / m)
//
//   s (e1[m] < e2[m], A)         = (A (e1) == A (e2))
//				    ? 1
//				    : c1 * (1 - (A(e2) - A(e1)) / 2^m)
//

// TODO failed assumptions -> no handling necessary, sls only works for SAT
int
btor_sat_aux_btor_sls (Btor *btor)
{
  assert (btor);
  // TODO we currently support QF_BV only
  assert (btor->lambdas->count == 0 && btor->ufs->count == 0);

  int i, j;
  int sat_result, simp_sat_result;

  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  simp_sat_result = btor_simplify (btor);
  btor_update_assumptions (btor);

  if (btor->inconsistent) goto UNSAT;

  // do something

  // TODO insert infinite model here
  i = 1;
  /* Generate intial model, all bv vars are initialized with zero.
   * We do not have to consider model_for_all_nodes, but let this be handled
   * by the model generation (if enabled) after SAT has been determined. */
  btor_generate_model (btor, 0);

  for (j = 0; j < BTOR_SLS_MAXSTEPS (i); j++)
  {
    // select candidate
    // find best move
    // if move update
    // else randomize
  }

UNSAT:
  sat_result = BTOR_UNSAT;
  goto DONE;

DONE:
  btor->last_sat_result = sat_result;
  return sat_result;
}

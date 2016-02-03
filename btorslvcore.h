/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLVCORE_H_INCLUDED
#define BTORSLVCORE_H_INCLUDED

#include "btorexp.h"
#include "btorslv.h"
#include "utils/btorhashptr.h"

#define BTOR_CORE_SOLVER(btor) ((BtorCoreSolver *) (btor)->slv)

struct BtorCoreSolver
{
  BTOR_SOLVER_STRUCT;

  BtorPtrHashTable *lemmas;
  BtorNodePtrStack cur_lemmas;

  BtorPtrHashTable *score; /* dcr score */

  // TODO (ma): make options for these
  int lod_limit;
  int sat_limit;
  bool assume_lemmas;

  /* compare fun for sorting the inputs in search_inital_applies_dual_prop */
  int (*dp_cmp_inputs) (const void *, const void *);

  struct
  {
    int lod_refinements; /* number of lemmas on demand refinements */
    int refinement_iterations;

    int function_congruence_conflicts;
    int beta_reduction_conflicts;
    int extensionality_lemmas;

    BtorIntStack lemmas_size;      /* distribution of n-size lemmas */
    long long int lemmas_size_sum; /* sum of the size of all added lemmas */

    int dp_failed_vars; /* number of vars in FA (dual prop) of last
                           sat call (final bv skeleton) */
    int dp_assumed_vars;
    int dp_failed_applies; /* number of applies in FA (dual prop) of last
                              sat call (final bv skeleton) */
    int dp_assumed_applies;
    int dp_failed_eqs;
    int dp_assumed_eqs;

    long long eval_exp_calls;
    long long propagations;
    long long propagations_down;
    long long partial_beta_reduction_restarts;
  } stats;

  struct
  {
    double sat;
    double eval;
    double search_init_apps;
    double search_init_apps_compute_scores;
    double search_init_apps_compute_scores_merge_applies;
    double search_init_apps_cloning;
    double search_init_apps_sat;
    double search_init_apps_collect_var_apps;
    double search_init_apps_collect_fa;
    double search_init_apps_collect_fa_cone;
    double lemma_gen;
    double find_nenc_app;
    double find_prop_app;
    double find_cond_prop_app;
  } time;
};

typedef struct BtorCoreSolver BtorCoreSolver;

BtorSolver *btor_new_core_solver (Btor *btor);

// TODO (ma): this is just a fix for now, this should be moved elsewhere
/* Evaluates expression and returns its value. */
BtorBitVector *btor_eval_exp (Btor *btor, BtorNode *exp);
#endif

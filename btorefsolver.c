/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorefsolver.h"

BtorSolverKind kind;
struct
{
  void *(*clone) (Btor *, Btor *, BtorNodeMap *);
  void (*delet) (Btor *);
  int (*sat) (Btor *, int, int);
  void (*generate_model) (Btor *, int, int);
  void (*print_stats) (Btor *);
  void (*print_time_stats) (Btor *);
} api;

static BtorSolver *
clone_ef_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  return 0;
}

static void
delete_ef_solver (Btor *)
{
}

static int
sat_ef_solver (Btor * btor, int lod_limit, int

BtorSolver *
btor_new_ef_solver (Btor * btor)
{
  assert (btor);

  BtorEFSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind                 = BTOR_EF_SOLVER_KIND;
  slv->api.clone            = clone_core_solver;
  slv->api.delet            = delete_core_solver;
  slv->api.sat              = sat_core_solver;
  slv->api.generate_model   = generate_model_core_solver;
  slv->api.print_stats      = print_stats_core_solver;
  slv->api.print_time_stats = print_time_stats_core_solver;

  slv->lemmas = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (slv->cur_lemmas);

  BTOR_INIT_STACK (slv->stats.lemmas_size);

  BTOR_MSG (btor->msg, 1, "enabled core engine");

  return (BtorSolver *) slv;
}

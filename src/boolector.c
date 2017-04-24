/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2016 Armin Biere.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/

#include "boolector.h"
#include "btorabort.h"
#include "btorchkclone.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btorexit.h"
#include "btormodel.h"
#include "btorparse.h"
#include "btorprintmodel.h"
#include "btorsat.h"
#include "btorsort.h"
#include "btortrapi.h"
#include "dumper/btordumpaig.h"
#include "dumper/btordumpbtor.h"
#include "dumper/btordumpsmt.h"
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

#include <limits.h>
#include <stdio.h>
#include <string.h>

/*------------------------------------------------------------------------*/

static void
inc_sort_ext_ref_counter (Btor *btor, BtorSortId id)
{
  assert (btor);
  assert (id);

  BtorSort *sort;
  sort = btor_get_sort_by_id (btor, id);

  BTOR_ABORT (sort->ext_refs == INT_MAX, "Node reference counter overflow");
  sort->ext_refs += 1;
  btor->external_refs += 1;
}

static void
dec_sort_ext_ref_counter (Btor *btor, BtorSortId id)
{
  assert (btor);
  assert (id);

  BtorSort *sort;
  sort = btor_get_sort_by_id (btor, id);
  assert (sort->ext_refs > 0);
  sort->ext_refs -= 1;
  btor->external_refs -= 1;
}

/*------------------------------------------------------------------------*/

void
boolector_chkclone (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");

#ifndef NDEBUG
  BtorBVAss *bvass, *cbvass;
  BtorBVAssList *bvasslist, *cbvasslist;
  BtorFunAss *funass, *cfunass;
  BtorFunAssList *funasslist, *cfunasslist;
  char **indices, **values, **cindices, **cvalues;
  int32_t i;

  if (btor->clone)
  {
    /* force auto cleanup (might have been disabled via btormbt) */
    btor_opt_set (btor->clone, BTOR_OPT_AUTO_CLEANUP, 1);
    btor_delete_btor (btor->clone);
    btor->clone = 0;
  }
  /* do not generate shadow clone if sat solver does not support cloning
   * (else only expression layer will be cloned and shadowed API function
   *  calls may fail) */
  if (!btor_sat_mgr_has_clone_support (btor_get_sat_mgr_btor (btor))) return;
  btor->clone           = btor_clone_btor (btor);
  btor->clone->apitrace = 0; /* disable tracing of shadow clone */
  assert (btor->clone->mm);
  assert ((!btor->avmgr && !btor->clone->avmgr)
          || (btor->avmgr && btor->clone->avmgr));
  /* update assignment lists */
  bvasslist  = btor->bv_assignments;
  cbvasslist = btor->clone->bv_assignments;
  for (bvass = bvasslist->first, cbvass = cbvasslist->first; bvass;
       bvass = bvass->next, cbvass = cbvass->next)
  {
    assert (cbvass);
    assert (
        !strcmp (btor_ass_get_bv_str (bvass), btor_ass_get_bv_str (cbvass)));
    bvass->cloned_assignment = btor_ass_get_bv_str (cbvass);
  }
  funasslist  = btor->fun_assignments;
  cfunasslist = btor->clone->fun_assignments;
  for (funass = funasslist->first, cfunass = cfunasslist->first; funass;
       funass = funass->next, cfunass = cfunass->next)
  {
    assert (cfunass);
    assert (funass->size == cfunass->size);
    btor_ass_get_fun_indices_values (funass, &indices, &values, funass->size);
    btor_ass_get_fun_indices_values (
        cfunass, &cindices, &cvalues, cfunass->size);
    for (i = 0; i < funass->size; i++)
    {
      assert (!strcmp (indices[i], cindices[i]));
      assert (!strcmp (values[i], cvalues[i]));
    }
    funass->cloned_indices = cindices;
    funass->cloned_values  = cvalues;
  }
  btor_chkclone (btor, btor->clone);
#endif
}

#ifndef NDEBUG
#define BTOR_CLONED_EXP(exp)                                                 \
  ((btor->clone ? BTOR_EXPORT_BOOLECTOR_NODE (                               \
                      BTOR_IS_INVERTED_NODE (exp)                            \
                          ? BTOR_INVERT_NODE (BTOR_PEEK_STACK (              \
                                btor->clone->nodes_id_table,                 \
                                BTOR_REAL_ADDR_NODE (exp)->id))              \
                          : BTOR_PEEK_STACK (btor->clone->nodes_id_table,    \
                                             BTOR_REAL_ADDR_NODE (exp)->id)) \
                : 0))

#else
#define BTOR_CLONED_EXP(exp) 0
#endif

/*------------------------------------------------------------------------*/

/* for internal use (parser), only */

void
boolector_set_btor_id (Btor *btor, BoolectorNode *node, int id)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d", id);
  BTOR_ABORT (!btor_is_bv_var_node (exp) && !btor_is_uf_array_node (exp),
              "'exp' is neither BV/array variable nor UF");
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  btor_exp_set_btor_id (btor, exp, id);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_btor_id, BTOR_CLONED_EXP (exp), id);
#endif
}

BtorMsg *
boolector_get_btor_msg (Btor *btor)
{
  BtorMsg *res;
  /* do not trace, clutters the trace unnecessarily */
  res = btor->msg;
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (get_btor_msg);
#endif
  return res;
}

void
boolector_print_value_smt2 (Btor *btor,
                            BoolectorNode *node,
                            char *symbol_str,
                            FILE *file)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI_UNFUN_EXT (exp, "%s", symbol_str);
  BTOR_ABORT_ARG_NULL (file);
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN),
              "model generation has not been enabled");
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  btor_print_value_smt2 (btor, exp, symbol_str, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (
      print_value_smt2, BTOR_CLONED_EXP (exp), symbol_str, file);
#endif
}

/*------------------------------------------------------------------------*/

Btor *
boolector_new (void)
{
  char *trname;
  Btor *btor;

  btor = btor_new_btor ();
  if ((trname = getenv ("BTORAPITRACE"))) btor_open_apitrace (btor, trname);
  BTOR_TRAPI ("");
  BTOR_TRAPI_RETURN_PTR (btor);
  return btor;
}

Btor *
boolector_clone (Btor *btor)
{
  Btor *clone;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  clone = btor_clone_btor (btor);
  BTOR_TRAPI_RETURN_PTR (clone);
#ifndef NDEBUG
  if (btor->clone)
  {
    Btor *cshadow = boolector_clone (btor->clone);
    btor_chkclone (btor->clone, cshadow);
    btor_delete_btor (cshadow);
  }
#endif
  return clone;
}

void
boolector_delete (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  if (btor->close_apitrace == 1)
    fclose (btor->apitrace);
  else if (btor->close_apitrace == 2)
    pclose (btor->apitrace);
#ifndef NDEBUG
  if (btor->clone) boolector_delete (btor->clone);
#endif
  btor_delete_btor (btor);
}

void
boolector_set_term (Btor *btor, int (*fun) (void *), void *state)
{
  BTOR_ABORT_ARG_NULL (btor);
  btor_set_term_btor (btor, fun, state);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_term, fun, state);
#endif
}

int
boolector_terminate (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL (btor);
  res = btor_terminate_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, terminate);
#endif
  return res;
}

void
boolector_set_msg_prefix (Btor *btor, const char *prefix)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%s", prefix);
  btor_set_msg_prefix_btor (btor, prefix);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_msg_prefix, prefix);
#endif
}

int
boolector_get_refs (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  res = btor->external_refs;
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_refs);
#endif
  return res;
}

void
boolector_reset_time (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  btor_reset_time_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_time);
#endif
}

void
boolector_reset_stats (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  btor_reset_stats_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_stats);
#endif
}

void
boolector_print_stats (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  btor_sat_print_stats (btor_get_sat_mgr_btor (btor));
  btor_print_stats_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (print_stats);
#endif
}

void
boolector_set_trapi (Btor *btor, FILE *apitrace)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (btor->apitrace, "API trace already set");
  btor->apitrace = apitrace;
}

FILE *
boolector_get_trapi (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  return btor->apitrace;
}

/*------------------------------------------------------------------------*/

void
boolector_assert (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (btor_get_exp_width (btor, exp) != 1,
              "'exp' must have bit-width one");
  BTOR_ABORT (BTOR_REAL_ADDR_NODE (exp)->parameterized,
              "assertion must not be parameterized");
  btor_assert_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (assert, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_assume (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL),
              "incremental usage has not been enabled");
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (btor_get_exp_width (btor, exp) != 1,
              "'exp' must have bit-width one");
  BTOR_ABORT (BTOR_REAL_ADDR_NODE (exp)->parameterized,
              "assumption must not be parameterized");
  btor_assume_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (assume, BTOR_CLONED_EXP (exp));
#endif
}

bool
boolector_failed (Btor *btor, BoolectorNode *node)
{
  bool res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (btor->last_sat_result != BTOR_RESULT_UNSAT,
              "cannot check failed assumptions if input formula is not UNSAT");
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL),
              "incremental usage has not been enabled");
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (btor_get_exp_width (btor, exp) != 1,
              "'exp' must have bit-width one");
  BTOR_ABORT (!btor_is_assumption_exp (btor, exp),
              "'exp' must be an assumption");
  res = btor_failed_exp (btor, exp);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, failed, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

void
boolector_fixate_assumptions (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT (
      !btor_opt_get (btor, BTOR_OPT_INCREMENTAL),
      "incremental usage has not been enabled, no assumptions available");
  btor_fixate_assumptions (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (fixate_assumptions);
#endif
}

void
boolector_reset_assumptions (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT (
      !btor_opt_get (btor, BTOR_OPT_INCREMENTAL),
      "incremental usage has not been enabled, no assumptions available");
  btor_reset_assumptions (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_assumptions);
#endif
}

int
boolector_sat (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
                  && btor->btor_sat_btor_called > 0,
              "incremental usage has not been enabled."
              "'boolector_sat' may only be called once");
  res = btor_sat_btor (btor, -1, -1);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, sat);
#endif
  return res;
}

int
boolector_limited_sat (Btor *btor, int lod_limit, int sat_limit)
{
  int res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d %d", lod_limit, sat_limit);
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
                  && btor->btor_sat_btor_called > 0,
              "incremental usage has not been enabled."
              "'boolector_limited_sat' may only be called once");
  res = btor_sat_btor (btor, lod_limit, sat_limit);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, limited_sat, lod_limit, sat_limit);
#endif
  return res;
}

int
boolector_simplify (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");

  res = btor_simplify (btor);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, simplify);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

int
boolector_set_sat_solver (Btor *btor, const char *solver)
{
  uint32_t sat_engine;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%s", solver);
  BTOR_ABORT_ARG_NULL (solver);
  BTOR_ABORT (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");

  sat_engine = BTOR_SAT_ENGINE_DFLT;

#ifdef BTOR_USE_LINGELING
  if (!strcasecmp (solver, "lingeling"))
    sat_engine = BTOR_SAT_ENGINE_LINGELING;
  else
#endif
#ifdef BTOR_USE_PICOSAT
      if (!strcasecmp (solver, "picosat"))
    sat_engine = BTOR_SAT_ENGINE_PICOSAT;
  else
#endif
#ifdef BTOR_USE_MINISAT
      if (!strcasecmp (solver, "minisat"))
    sat_engine = BTOR_SAT_ENGINE_MINISAT;
  else
#endif
    BTOR_ABORT (1, "invalid sat engine '%s' selected", solver);

  btor_opt_set (btor, BTOR_OPT_SAT_ENGINE, sat_engine);
  BTOR_TRAPI_RETURN_INT (1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_sat_solver, solver);
#endif
  return 1;
}

#ifdef BTOR_USE_LINGELING
int
boolector_set_sat_solver_lingeling (Btor *btor, const char *optstr, int nofork)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%s %d", optstr, nofork);
  BTOR_ABORT (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  btor_opt_set (btor, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_LINGELING);
  btor_opt_set_str (btor, BTOR_OPT_SAT_ENGINE, optstr);
  btor_opt_set (btor, BTOR_OPT_SAT_ENGINE_LGL_FORK, nofork ? 0 : 1);
  BTOR_TRAPI_RETURN_INT (1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_sat_solver_lingeling, optstr, nofork);
#endif
  return 1;
}
#endif

#ifdef BTOR_USE_PICOSAT
int
boolector_set_sat_solver_picosat (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  btor_opt_set (btor, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_PICOSAT);
  BTOR_TRAPI_RETURN_INT (1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_sat_solver_picosat);
#endif
  return 1;
}
#endif

#ifdef BTOR_USE_MINISAT
int
boolector_set_sat_solver_minisat (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  btor_opt_set (btor, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_MINISAT);
  BTOR_TRAPI_RETURN_INT (1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_sat_solver_minisat);
#endif
  return 1;
}
#endif

/*------------------------------------------------------------------------*/

void
boolector_set_opt (Btor *btor, BtorOption opt, uint32_t val)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d %s %d", opt, btor_opt_get_lng (btor, opt), val);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  BTOR_ABORT (
      val < btor_opt_get_min (btor, opt) || val > btor_opt_get_max (btor, opt),
      "invalid option value '%u' for option '%s'",
      val,
      btor_opt_get_lng (btor, opt));

  if (val)
  {
    if (opt == BTOR_OPT_INCREMENTAL)
    {
      BTOR_ABORT (btor->btor_sat_btor_called > 0,
                  "enabling/disabling incremental usage must be done "
                  "before calling 'boolector_sat'");
      BTOR_ABORT (btor_opt_get (btor, BTOR_OPT_UCOPT),
                  "incremental solving cannot be enabled "
                  "if unconstrained optimization is enabled");
    }
    else if (opt == BTOR_OPT_MODEL_GEN)
    {
      BTOR_ABORT (btor_opt_get (btor, BTOR_OPT_UCOPT),
                  "model generation cannot be enabled "
                  "if unconstrained optimization is enabled");
    }
    else if (opt == BTOR_OPT_UCOPT)
    {
      BTOR_ABORT (btor_opt_get (btor, BTOR_OPT_MODEL_GEN),
                  "Unconstrained optimization cannot be enabled "
                  "if model generation is enabled");
      BTOR_ABORT (btor_opt_get (btor, BTOR_OPT_INCREMENTAL),
                  "Unconstrained optimization cannot be enabled "
                  "in incremental mode");
    }
    else if (opt == BTOR_OPT_FUN_DUAL_PROP)
    {
      BTOR_ABORT (val && btor_opt_get (btor, BTOR_OPT_FUN_JUST),
                  "enabling multiple optimization techniques is not allowed");
    }
    else if (opt == BTOR_OPT_FUN_JUST)
    {
      BTOR_ABORT (val && btor_opt_get (btor, BTOR_OPT_FUN_DUAL_PROP),
                  "enabling multiple optimization techniques is not allowed");
    }
    else if (opt == BTOR_OPT_UCOPT)
    {
      BTOR_ABORT (btor_opt_get (btor, BTOR_OPT_MODEL_GEN),
                  "Unconstrained optimization cannot be enabled "
                  "if model generation is enabled");
    }
  }

  if (opt == BTOR_OPT_REWRITE_LEVEL)
  {
    BTOR_ABORT (
        BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
        "setting rewrite level must be done before creating expressions");
  }

  btor_opt_set (btor, opt, val);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_opt, opt, val);
#endif
}

uint32_t
boolector_get_opt (Btor *btor, BtorOption opt)
{
  uint32_t res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  res = btor_opt_get (btor, opt);
  BTOR_TRAPI_RETURN_UINT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_opt, opt);
#endif
  return res;
}

uint32_t
boolector_get_opt_min (Btor *btor, BtorOption opt)
{
  uint32_t res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  res = btor_opt_get_min (btor, opt);
  BTOR_TRAPI_RETURN_UINT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_opt_min, opt);
#endif
  return res;
}

uint32_t
boolector_get_opt_max (Btor *btor, BtorOption opt)
{
  uint32_t res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  res = btor_opt_get_max (btor, opt);
  BTOR_TRAPI_RETURN_UINT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_opt_max, opt);
#endif
  return res;
}

uint32_t
boolector_get_opt_dflt (Btor *btor, BtorOption opt)
{
  uint32_t res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  res = btor_opt_get_dflt (btor, opt);
  BTOR_TRAPI_RETURN_UINT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_opt_dflt, opt);
#endif
  return res;
}

const char *
boolector_get_opt_lng (Btor *btor, BtorOption opt)
{
  const char *res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  res = btor_opt_get_lng (btor, opt);
  BTOR_TRAPI_RETURN_STR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_STR (res, get_opt_lng, opt);
#endif
  return res;
}

const char *
boolector_get_opt_shrt (Btor *btor, BtorOption opt)
{
  const char *res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  res = btor_opt_get_shrt (btor, opt);
  BTOR_TRAPI_RETURN_STR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_STR (res, get_opt_shrt, opt);
#endif
  return res;
}

const char *
boolector_get_opt_desc (Btor *btor, BtorOption opt)
{
  const char *res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  res = btor_opt_get_desc (btor, opt);
  BTOR_TRAPI_RETURN_STR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_STR (res, get_opt_desc, opt);
#endif
  return res;
}

bool
boolector_has_opt (Btor *btor, BtorOption opt)
{
  bool res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  res = btor_opt_is_valid (btor, opt);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, next_opt, opt);
#endif
  return res;
}

BtorOption
boolector_first_opt (Btor *btor)
{
  BtorOption res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  res = btor_opt_first (btor);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, first_opt);
#endif
  return res;
}

BtorOption
boolector_next_opt (Btor *btor, BtorOption opt)
{
  BtorOption res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", opt);
  BTOR_ABORT (!btor_opt_is_valid (btor, opt), "invalid option");
  res = btor_opt_next (btor, opt);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, next_opt, opt);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_copy (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_copy_exp (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, copy, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

void
boolector_release (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
#ifndef NDEBUG
  BoolectorNode *cexp = BTOR_CLONED_EXP (exp);
#endif
  assert (BTOR_REAL_ADDR_NODE (exp)->ext_refs);
  btor_dec_exp_ext_ref_counter (btor, exp);
  btor_release_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (release, cexp);
#endif
}

void
boolector_release_all (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  btor_release_all_ext_refs (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (release_all);
#endif
}

BoolectorNode *
boolector_const (Btor *btor, const char *bits)
{
  BtorNode *res;
  BtorBitVector *bv;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%s", bits);
  BTOR_ABORT_ARG_NULL (bits);
  BTOR_ABORT (*bits == '\0', "'bits' must not be empty");
  bv  = btor_bv_char_to_bv (btor->mm, (char *) bits);
  res = btor_const_exp (btor, bv);
  btor_inc_exp_ext_ref_counter (btor, res);
  btor_bv_free (btor->mm, bv);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, const, bits);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_zero (Btor *btor, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_zero_exp (btor, s);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, zero, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_false (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  res = btor_false_exp (btor);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, false);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ones (Btor *btor, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_ones_exp (btor, s);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ones, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_true (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  res = btor_true_exp (btor);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, true);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_one (Btor *btor, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_one_exp (btor, s);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, one, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_unsigned_int (Btor *btor, unsigned int u, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%u " SORT_FMT, u, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_unsigned_exp (btor, u, s);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, unsigned_int, u, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_int (Btor *btor, int i, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d " SORT_FMT, i, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_int_exp (btor, i, s);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, int, i, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_var (Btor *btor, BoolectorSort sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL (btor);

  BtorNode *res;
  char *symb;
  BtorSortId s;

  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, s),
              "'sort' is not a bit vector sort");
  symb = (char *) symbol;
  BTOR_TRAPI (SORT_FMT " %s", sort, btor, symb);
  BTOR_ABORT (symb && btor_get_ptr_hash_table (btor->symbols, (char *) symb),
              "symbol '%s' is already in use",
              symb);
  res = btor_var_exp (btor, s, symb);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
  (void) btor_add_ptr_hash_table (btor->inputs, btor_copy_exp (btor, res));
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, var, sort, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_array (Btor *btor, BoolectorSort sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL (btor);

  BtorNode *res;
  char *symb;
  BtorSortId s;

  symb = (char *) symbol;
  s    = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_fun_sort (btor, s)
                  || btor_get_arity_tuple_sort (
                         btor, btor_get_domain_fun_sort (btor, s))
                         != 1,
              "'sort' is not an array sort");
  BTOR_TRAPI (SORT_FMT " %s", sort, btor, symb);
  BTOR_ABORT (symb && btor_get_ptr_hash_table (btor->symbols, symb),
              "symbol '%s' is already in use",
              symb);
  res = btor_array_exp (btor, s, symb);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
  (void) btor_add_ptr_hash_table (btor->inputs, btor_copy_exp (btor, res));
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, array, sort, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uf (Btor *btor, BoolectorSort sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL (btor);

  BtorNode *res;
  BtorSortId s;
  char *symb;

  symb = (char *) symbol;
  s    = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_TRAPI (SORT_FMT "%s", sort, btor, symb);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_fun_sort (btor, s),
              "%ssort%s%s%s%s must be a function sort",
              symbol ? "" : "'",
              symbol ? "" : "'",
              symbol ? " '" : "",
              symbol ? symbol : "",
              symbol ? "'" : "");
  BTOR_ABORT (symb && btor_get_ptr_hash_table (btor->symbols, symb),
              "symbol '%s' is already in use",
              symb);

  res = btor_uf_exp (btor, s, symb);
  assert (BTOR_IS_REGULAR_NODE (res));
  btor_inc_exp_ext_ref_counter (btor, res);
  (void) btor_add_ptr_hash_table (btor->inputs, btor_copy_exp (btor, res));
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, uf, sort, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_not (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  res = btor_not_exp (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, not, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_neg (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  res = btor_neg_exp (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, neg, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redor (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  res = btor_redor_exp (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redor, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redxor (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  res = btor_redxor_exp (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redxor, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redand (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  res = btor_redand_exp (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redand, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slice (Btor *btor,
                 BoolectorNode *node,
                 uint32_t upper,
                 uint32_t lower)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d %d", upper, lower);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT ((uint32_t) upper >= btor_get_exp_width (btor, exp),
              "'upper' must not be >= width of 'exp'");
  res = btor_slice_exp (btor, exp, upper, lower);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slice, BTOR_CLONED_EXP (exp), upper, lower);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uext (Btor *btor, BoolectorNode *node, int width)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d", width);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (width < 0, "'width' must not be negative");
  res = btor_uext_exp (btor, exp, width);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, uext, BTOR_CLONED_EXP (exp), width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sext (Btor *btor, BoolectorNode *node, int width)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d", width);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (width < 0, "'width' must not be negative");
  res = btor_sext_exp (btor, exp, width);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sext, BTOR_CLONED_EXP (exp), width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_implies (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT (
      btor_get_exp_width (btor, e0) != 1 || btor_get_exp_width (btor, e1) != 1,
      "bit-width of 'e0' and 'e1' have be 1");
  res = btor_implies_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, implies, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_iff (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT (
      btor_get_exp_width (btor, e0) != 1 || btor_get_exp_width (btor, e1) != 1,
      "bit-width of 'e0' and 'e1' must not be unequal to 1");
  res = btor_iff_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, iff, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_xor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_xor_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, xor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_xnor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_xnor_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, xnor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_and (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_and_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, and, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_nand (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_nand_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nand, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_or (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_or_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, or, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_nor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_nor_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_eq (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT (btor_exp_get_sort_id (e0) != btor_exp_get_sort_id (e1),
              "nodes must have equal sorts");
  BTOR_ABORT (btor_is_fun_sort (btor, btor_exp_get_sort_id (e0))
                  && (BTOR_REAL_ADDR_NODE (e0)->parameterized
                      || BTOR_REAL_ADDR_NODE (e1)->parameterized),
              "parameterized function equalities not supported");
  res = btor_eq_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, eq, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ne (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT (btor_exp_get_sort_id (e0) != btor_exp_get_sort_id (e1),
              "nodes must have equal sorts");
  BTOR_ABORT (btor_is_fun_sort (btor, btor_exp_get_sort_id (e0))
                  && (BTOR_REAL_ADDR_NODE (e0)->parameterized
                      || BTOR_REAL_ADDR_NODE (e1)->parameterized),
              "parameterized function equalities not supported");
  res = btor_ne_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ne, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_add (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_add_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, add, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uaddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_uaddo_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, uaddo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_saddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_saddo_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, saddo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_mul (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_mul_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, mul, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_umulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_umulo_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, umulo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_smulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_smulo_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, smulo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ult (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_ult_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ult, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_slt_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ulte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_ulte_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ulte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_slte_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ugt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_ugt_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ugt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sgt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_sgt_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sgt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ugte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_ugte_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ugte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sgte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_sgte_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sgte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sll (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  len = btor_get_exp_width (btor, e0);
  BTOR_ABORT (!btor_is_power_of_2_util (len),
              "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT (btor_log_2_util (len) != btor_get_exp_width (btor, e1),
              "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_sll_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sll, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_srl (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  len = btor_get_exp_width (btor, e0);
  BTOR_ABORT (!btor_is_power_of_2_util (len),
              "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT (btor_log_2_util (len) != btor_get_exp_width (btor, e1),
              "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_srl_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, srl, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sra (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  len = btor_get_exp_width (btor, e0);
  BTOR_ABORT (!btor_is_power_of_2_util (len),
              "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT (btor_log_2_util (len) != btor_get_exp_width (btor, e1),
              "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_sra_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sra, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_rol (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *res;

  BTOR_ABORT_ARG_NULL (btor);
  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  len = btor_get_exp_width (btor, e0);
  BTOR_ABORT (!btor_is_power_of_2_util (len),
              "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT (btor_log_2_util (len) != btor_get_exp_width (btor, e1),
              "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_rol_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, rol, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ror (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  len = btor_get_exp_width (btor, e0);
  BTOR_ABORT (!btor_is_power_of_2_util (len),
              "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT (btor_log_2_util (len) != btor_get_exp_width (btor, e1),
              "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_ror_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ror, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sub (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_sub_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sub, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_usubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_usubo_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, usubo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ssubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_ssubo_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, ssubo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_udiv (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_udiv_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, udiv, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sdiv (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_sdiv_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sdiv, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sdivo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_sdivo_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, sdivo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_urem (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_urem_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, urem, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_srem (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_srem_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, srem, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_smod (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT_BW_MISMATCH (e0, e1);
  res = btor_smod_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, smod, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_concat (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  BTOR_ABORT_IS_NOT_BV (e0);
  BTOR_ABORT_IS_NOT_BV (e1);
  BTOR_ABORT (
      btor_get_exp_width (btor, e0) > INT_MAX - btor_get_exp_width (btor, e1),
      "bit-width of result is too large");
  res = btor_concat_exp (btor, e0, e1);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, concat, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_read (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index)
{
  BtorNode *e_array, *e_index, *res;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  e_index = BTOR_IMPORT_BOOLECTOR_NODE (n_index);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e_array);
  BTOR_ABORT_ARG_NULL (e_index);
  BTOR_TRAPI_BINFUN (e_array, e_index);
  BTOR_ABORT_REFS_NOT_POS (e_array);
  BTOR_ABORT_REFS_NOT_POS (e_index);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_array);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_index);
  BTOR_ABORT_IS_BV (e_array);
  BTOR_ABORT_IS_NOT_BV (e_index);
  BTOR_ABORT (
      btor_get_index_array_sort (btor, btor_exp_get_sort_id (e_array))
          != btor_exp_get_sort_id (e_index),
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  res = btor_read_exp (btor, e_array, e_index);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, read, BTOR_CLONED_EXP (e_array), BTOR_CLONED_EXP (e_index));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_write (Btor *btor,
                 BoolectorNode *n_array,
                 BoolectorNode *n_index,
                 BoolectorNode *n_value)
{
  BtorNode *e_array, *e_index, *e_value;
  BtorNode *res;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  e_index = BTOR_IMPORT_BOOLECTOR_NODE (n_index);
  e_value = BTOR_IMPORT_BOOLECTOR_NODE (n_value);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e_array);
  BTOR_ABORT_ARG_NULL (e_index);
  BTOR_ABORT_ARG_NULL (e_value);
  BTOR_TRAPI_TERFUN (e_array, e_index, e_value);
  BTOR_ABORT_REFS_NOT_POS (e_array);
  BTOR_ABORT_REFS_NOT_POS (e_index);
  BTOR_ABORT_REFS_NOT_POS (e_value);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_array);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_index);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_value);
  BTOR_ABORT_IS_BV (e_array);
  BTOR_ABORT_IS_NOT_BV (e_index);
  BTOR_ABORT_IS_NOT_BV (e_value);
  BTOR_ABORT (
      btor_get_index_array_sort (btor, btor_exp_get_sort_id (e_array))
          != btor_exp_get_sort_id (e_index),
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  BTOR_ABORT (btor_get_element_array_sort (btor, btor_exp_get_sort_id (e_array))
                  != btor_exp_get_sort_id (e_value),
              "element bit-width of 'e_array' and bit-width of 'e_value' must "
              "be equal");
  res = btor_write_exp (btor, e_array, e_index, e_value);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res,
                         write,
                         BTOR_CLONED_EXP (e_array),
                         BTOR_CLONED_EXP (e_index),
                         BTOR_CLONED_EXP (e_value));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_cond (Btor *btor,
                BoolectorNode *n_cond,
                BoolectorNode *n_then,
                BoolectorNode *n_else)
{
  BtorNode *e_cond, *e_if, *e_else;
  BtorNode *res;

  e_cond = BTOR_IMPORT_BOOLECTOR_NODE (n_cond);
  e_if   = BTOR_IMPORT_BOOLECTOR_NODE (n_then);
  e_else = BTOR_IMPORT_BOOLECTOR_NODE (n_else);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e_cond);
  BTOR_ABORT_ARG_NULL (e_if);
  BTOR_ABORT_ARG_NULL (e_else);
  BTOR_TRAPI_TERFUN (e_cond, e_if, e_else);
  BTOR_ABORT_REFS_NOT_POS (e_cond);
  BTOR_ABORT_REFS_NOT_POS (e_if);
  BTOR_ABORT_REFS_NOT_POS (e_else);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_cond);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_if);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_else);
  BTOR_ABORT_IS_NOT_BV (e_cond);
  BTOR_ABORT (btor_get_exp_width (btor, e_cond) != 1,
              "bit-width of 'e_cond' must be equal to 1");
  BTOR_ABORT (btor_exp_get_sort_id (e_if) != btor_exp_get_sort_id (e_else),
              "sorts of 'e_if' and 'e_else' branch must be equal");
  res = btor_cond_exp (btor, e_cond, e_if, e_else);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res,
                         cond,
                         BTOR_CLONED_EXP (e_cond),
                         BTOR_CLONED_EXP (e_if),
                         BTOR_CLONED_EXP (e_else));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_param (Btor *btor, BoolectorSort sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL (btor);

  BtorNode *res;
  char *symb;
  BtorSortId s;

  symb = (char *) symbol;
  BTOR_TRAPI (SORT_FMT " %s", sort, btor, symb);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, s),
              "'sort' is not a bit vector sort");
  BTOR_ABORT (symb && btor_get_ptr_hash_table (btor->symbols, symb),
              "symbol '%s' is already in use",
              symb);
  res = btor_param_exp (btor, s, symb);
  btor_inc_exp_ext_ref_counter (btor, res);

  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, param, sort, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_fun (Btor *btor,
               BoolectorNode **param_nodes,
               int paramc,
               BoolectorNode *node)
{
  int i, len;
  char *strtrapi;
  BtorNode **params, *exp, *res;

  params = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (param_nodes);
  exp    = BTOR_IMPORT_BOOLECTOR_NODE (node);

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (params);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT (paramc < 1, "'paramc' must not be < 1");

  len = 5 + 10 + paramc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "%d ", paramc);

  for (i = 0; i < paramc; i++)
  {
    BTOR_ABORT (!params[i] || !btor_is_param_node (params[i]),
                "'params[%d]' is not a parameter",
                i);
    BTOR_ABORT_REFS_NOT_POS (params[i]);
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (params[i]));
  }
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (exp));
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  BTOR_ABORT (btor_is_uf_node (btor_simplify_exp (btor, exp)),
              "expected bit vector term as function body");
  res = btor_fun_exp (btor, params, paramc, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BoolectorNode *cparam_nodes[paramc];
  for (i = 0; btor->clone && i < paramc; i++)
    cparam_nodes[i] = BTOR_CLONED_EXP (params[i]);
  BTOR_CHKCLONE_RES_PTR (res, fun, cparam_nodes, paramc, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_apply (Btor *btor,
                 BoolectorNode **arg_nodes,
                 int argc,
                 BoolectorNode *n_fun)
{
  int i, len;
  char *strtrapi;
  BtorNode **args, *e_fun, *res;

  args  = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);
  e_fun = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e_fun);

  BTOR_ABORT_REFS_NOT_POS (n_fun);
  BTOR_ABORT_BTOR_MISMATCH (btor, n_fun);

  len = 7 + 10 + argc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "%d ", argc);

  for (i = 0; i < argc; i++)
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (e_fun));

  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);

  BTOR_ABORT (!btor_is_fun_sort (btor, btor_exp_get_sort_id (e_fun)),
              "'e_fun' must be a function");
  BTOR_ABORT (
      (uint32_t) argc != btor_get_fun_arity (btor, e_fun),
      "number of arguments must be equal to the number of parameters in "
      "'e_fun'");
  BTOR_ABORT (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT (argc >= 1 && !args, "no arguments given but argc defined > 0");
  i = btor_fun_sort_check (btor, args, argc, e_fun);
  BTOR_ABORT (i >= 0, "invalid argument given at position %d", i);
  res = btor_apply_exps (btor, args, argc, e_fun);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES_PTR (res, apply, carg_nodes, argc, BTOR_CLONED_EXP (e_fun));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_inc (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);

  res = btor_inc_exp (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, inc, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_dec (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);

  res = btor_dec_exp (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, dec, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

Btor *
boolector_get_btor (BoolectorNode *node)
{
  BtorNode *exp, *real_exp;
  Btor *btor;
  BTOR_ABORT_ARG_NULL (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_REFS_NOT_POS (exp);
  real_exp = BTOR_REAL_ADDR_NODE (exp);
  btor     = real_exp->btor;
  BTOR_TRAPI_UNFUN (exp);
  BTOR_TRAPI_RETURN_PTR (btor);
#ifndef NDEBUG
  if (btor->clone)
  {
    Btor *clone = boolector_get_btor (BTOR_CLONED_EXP (exp));
    assert (clone == btor->clone);
    btor_chkclone (btor, btor->clone);
  }
#endif
  return btor;
}

int32_t
boolector_get_id (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (node);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_exp_get_id (BTOR_REAL_ADDR_NODE (exp));
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_id, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

BoolectorSort
boolector_get_sort (Btor *btor, const BoolectorNode *node)
{
  BtorNode *exp;
  BtorSortId res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_TRAPI_UNFUN (exp);
  res = btor_exp_get_sort_id (exp);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, get_sort, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort
boolector_fun_get_domain_sort (Btor *btor, const BoolectorNode *node)
{
  BtorNode *exp;
  BtorSortId res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT (!btor_is_fun_node (btor_simplify_exp (btor, exp)),
              "node must be a function node");
  BTOR_TRAPI_UNFUN (exp);
  res = ((BtorFunSort) btor_get_sort_by_id (btor, btor_exp_get_sort_id (exp))
             ->fun)
            .domain->id;
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, fun_get_domain_sort, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort
boolector_fun_get_codomain_sort (Btor *btor, const BoolectorNode *node)
{
  BtorNode *exp;
  BtorSortId res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT (!btor_is_fun_node (btor_simplify_exp (btor, exp)),
              "node must be a function node");
  BTOR_TRAPI_UNFUN (exp);
  res = ((BtorFunSort) btor_get_sort_by_id (btor, btor_exp_get_sort_id (exp))
             ->fun)
            .codomain->id;
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, fun_get_codomain_sort, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorNode *
boolector_match_node_by_id (Btor *btor, int id)
{
  BtorNode *res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (id <= 0, "node id must be > 0");
  BTOR_TRAPI ("%d", id);
  res = btor_match_node_by_id (btor, id);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, match_node_by_id, id);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_match_node_by_symbol (Btor *btor, const char *symbol)
{
  BtorNode *res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (symbol);
  BTOR_TRAPI ("%s", symbol);
  res = btor_match_node_by_symbol (btor, symbol);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, match_node_by_symbol, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_match_node (Btor *btor, BoolectorNode *node)
{
  BtorNode *res, *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  res = btor_match_node (btor, exp);
  btor_inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, match_node, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

const char *
boolector_get_symbol (Btor *btor, BoolectorNode *node)
{
  const char *res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = (const char *) btor_get_symbol_exp (btor, exp);
  BTOR_TRAPI_RETURN_STR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_STR (res, get_symbol, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

void
boolector_set_symbol (Btor *btor, BoolectorNode *node, const char *symbol)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_ABORT_ARG_NULL (symbol);
  BTOR_TRAPI_UNFUN_EXT (exp, "%s", symbol);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  btor_set_symbol_exp (btor, exp, symbol);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_symbol, BTOR_CLONED_EXP (exp), symbol);
#endif
}

uint32_t
boolector_get_width (Btor *btor, BoolectorNode *node)
{
  uint32_t res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  if (btor_is_fun_sort (btor, btor_exp_get_sort_id (exp)))
    res = btor_get_fun_exp_width (btor, exp);
  else
    res = btor_get_exp_width (btor, exp);
  BTOR_TRAPI_RETURN_UINT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_width, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

uint32_t
boolector_get_index_width (Btor *btor, BoolectorNode *n_array)
{
  uint32_t res;
  BtorNode *e_array;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e_array);
  BTOR_TRAPI_UNFUN (e_array);
  BTOR_ABORT_REFS_NOT_POS (e_array);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_array);
  BTOR_ABORT_IS_BV (e_array);
  BTOR_ABORT (btor_get_fun_arity (btor, e_array) > 1,
              "'n_array' is a function with arity > 1");
  res = btor_get_index_exp_width (btor, e_array);
  BTOR_TRAPI_RETURN_UINT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_index_width, BTOR_CLONED_EXP (e_array));
#endif
  return res;
}

const char *
boolector_get_bits (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *real;
  BtorBVAss *bvass;
  char *bits;
  const char *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL (node);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT (!btor_is_bv_const_node (exp), "argument is not a constant node");
  real = BTOR_REAL_ADDR_NODE (exp);
  /* representations of bits of const nodes are maintained analogously
   * to bv assignment strings */
  if (!BTOR_IS_INVERTED_NODE (exp))
    bits = btor_bv_to_char (btor->mm, btor_const_get_bits (exp));
  else
    bits = btor_bv_to_char (btor->mm, btor_const_get_invbits (real));
  bvass = btor_ass_new_bv (btor->bv_assignments, bits);
  btor_freestr (btor->mm, bits);
  res = btor_ass_get_bv_str (bvass);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  if (btor->clone)
  {
    const char *cloneres =
        boolector_get_bits (btor->clone, BTOR_CLONED_EXP (node));
    assert (!strcmp (cloneres, res));
    bvass->cloned_assignment = cloneres;
    btor_chkclone (btor, btor->clone);
  }
#endif
  return res;
}

void
boolector_free_bits (Btor *btor, const char *bits)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%p", bits);
  BTOR_ABORT_ARG_NULL (bits);
#ifndef NDEBUG
  char *cass;
  cass = (char *) btor_ass_get_bv ((const char *) bits)->cloned_assignment;
#endif
  btor_ass_release_bv (btor->bv_assignments, bits);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (free_bits, cass);
#endif
}

uint32_t
boolector_get_fun_arity (Btor *btor, BoolectorNode *node)
{
  uint32_t res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT (!btor_is_fun_node (btor_simplify_exp (btor, exp)),
              "given expression is not a function node");
  res = btor_get_fun_arity (btor, exp);
  BTOR_TRAPI_RETURN_UINT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_fun_arity, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

bool
boolector_is_const (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;
  bool res;
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  res = btor_is_bv_const_node (exp);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_const, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

bool
boolector_is_var (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;
  bool res;
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_is_bv_var_node (btor_simplify_exp (btor, exp));
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_var, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

bool
boolector_is_array (Btor *btor, BoolectorNode *node)
{
  bool res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_is_array_node (btor_simplify_exp (btor, exp));
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_array, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

bool
boolector_is_array_var (Btor *btor, BoolectorNode *node)
{
  bool res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_is_uf_array_node (btor_simplify_exp (btor, exp));
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_array_var, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

bool
boolector_is_param (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;
  bool res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_is_param_node (btor_simplify_exp (btor, exp));
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_param, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

bool
boolector_is_bound_param (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;
  bool res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT (!btor_is_param_node (btor_simplify_exp (btor, exp)),
              "given expression is not a parameter node");
  res = btor_param_is_bound (exp);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_bound_param, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

bool
boolector_is_uf (Btor *btor, BoolectorNode *node)
{
  bool res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_is_uf_node (btor_simplify_exp (btor, exp));
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_uf, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

bool
boolector_is_fun (Btor *btor, BoolectorNode *node)
{
  bool res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_is_fun_node (btor_simplify_exp (btor, exp));
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_fun, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int32_t
boolector_fun_sort_check (Btor *btor,
                          BoolectorNode **arg_nodes,
                          int argc,
                          BoolectorNode *n_fun)
{
  BtorNode **args, *e_fun;
  char *strtrapi;
  int i, len;
  int32_t res;

  args  = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);
  e_fun = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e_fun);
  BTOR_ABORT (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT (argc >= 1 && !args, "no arguments given but argc defined > 0");

  len = 15 + 10 + argc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "%d ", argc);

  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_ARG_NULL (args[i]);
    BTOR_ABORT_REFS_NOT_POS (args[i]);
    BTOR_ABORT_BTOR_MISMATCH (btor, args[i]);
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
  }
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (e_fun));
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  res = btor_fun_sort_check (btor, args, argc, e_fun);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES (
      res, fun_sort_check, carg_nodes, argc, BTOR_CLONED_EXP (e_fun));
#endif
  return res;
}

const char *
boolector_bv_assignment (Btor *btor, BoolectorNode *node)
{
  char *ass;
  const char *res;
  BtorNode *exp;
  BtorBVAss *bvass;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (btor->last_sat_result != BTOR_RESULT_SAT,
              "cannot retrieve model if input formula is not SAT");
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN),
              "model generation has not been enabled");
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  ass   = btor_bv_to_char (btor->mm, btor_model_get_bv (btor, exp));
  bvass = btor_ass_new_bv (btor->bv_assignments, ass);
  btor_freestr (btor->mm, ass);
  res = btor_ass_get_bv_str (bvass);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  if (btor->clone)
  {
    const char *cloneres =
        boolector_bv_assignment (btor->clone, BTOR_CLONED_EXP (exp));
    assert (!strcmp (cloneres, res));
    bvass->cloned_assignment = cloneres;
    btor_chkclone (btor, btor->clone);
  }
#endif
  return res;
}

void
boolector_free_bv_assignment (Btor *btor, const char *assignment)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%p", assignment);
  BTOR_ABORT_ARG_NULL (assignment);
#ifndef NDEBUG
  char *cass;
  cass =
      (char *) btor_ass_get_bv ((const char *) assignment)->cloned_assignment;
#endif
  btor_ass_release_bv (btor->bv_assignments, assignment);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (free_bv_assignment, cass);
#endif
}

static void
generate_fun_model_str (
    Btor *btor, BtorNode *exp, char ***args, char ***values, int *size)
{
  assert (btor);
  assert (exp);
  assert (args);
  assert (values);
  assert (size);
  assert (BTOR_IS_REGULAR_NODE (exp));

  char *arg, *tmp, *bv;
  uint32_t i, j, len;
  BtorPtrHashTableIterator it;
  const BtorPtrHashTable *model;
  BtorBitVector *value;
  BtorBitVectorTuple *t;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_is_fun_node (exp));

  model = btor_model_get_fun_aux (btor, btor->bv_model, btor->fun_model, exp);

  if ((btor_is_lambda_node (exp) && btor_get_fun_arity (btor, exp) > 1)
      || !btor->fun_model || !model)
  {
    *size = 0;
    return;
  }

  assert (model->count > 0);

  *size = (int) model->count;
  BTOR_NEWN (btor->mm, *args, *size);
  BTOR_NEWN (btor->mm, *values, *size);

  i = 0;
  btor_init_ptr_hash_table_iterator (&it, (BtorPtrHashTable *) model);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    value = (BtorBitVector *) it.bucket->data.as_ptr;

    /* build assignment string for all arguments */
    t   = (BtorBitVectorTuple *) btor_next_ptr_hash_table_iterator (&it);
    len = t->arity;
    for (j = 0; j < t->arity; j++) len += t->bv[j]->width;
    BTOR_NEWN (btor->mm, arg, len);
    tmp = arg;

    bv = btor_bv_to_char (btor->mm, t->bv[0]);
    strcpy (tmp, bv);
    btor_freestr (btor->mm, bv);

    for (j = 1; j < t->arity; j++)
    {
      bv = btor_bv_to_char (btor->mm, t->bv[j]);
      strcat (tmp, " ");
      strcat (tmp, bv);
      btor_freestr (btor->mm, bv);
    }
    assert (strlen (arg) == len - 1);

    (*args)[i]   = arg;
    (*values)[i] = (char *) btor_bv_to_char (btor->mm, value);
    i++;
  }
}

static void
fun_assignment (Btor *btor,
                BtorNode *n,
                char ***args,
                char ***values,
                int *size,
                BtorFunAss **ass)
{
  assert (btor);
  assert (n);
  assert (args);
  assert (values);
  assert (size);
  assert (BTOR_IS_REGULAR_NODE (n));

  int i;
  char **a = 0, **v = 0;

  *ass = 0;
  generate_fun_model_str (btor, n, &a, &v, size);

  if (*size)
  {
    *ass = btor_ass_new_fun (btor->fun_assignments, a, v, *size);
    for (i = 0; i < *size; i++)
    {
      btor_freestr (btor->mm, a[i]);
      btor_freestr (btor->mm, v[i]);
    }
    btor_free (btor->mm, a, *size * sizeof (*a));
    btor_free (btor->mm, v, *size * sizeof (*v));
    btor_ass_get_fun_indices_values (*ass, args, values, *size);
  }
}

void
boolector_array_assignment (Btor *btor,
                            BoolectorNode *n_array,
                            char ***indices,
                            char ***values,
                            int *size)
{
  BtorNode *e_array;
  BtorFunAss *ass;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (btor->last_sat_result != BTOR_RESULT_SAT,
              "cannot retrieve model if input formula is not SAT");
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN),
              "model generation has not been enabled");
  BTOR_ABORT_ARG_NULL (e_array);
  BTOR_TRAPI_UNFUN (e_array);
  BTOR_ABORT_ARG_NULL (indices);
  BTOR_ABORT_ARG_NULL (values);
  BTOR_ABORT_ARG_NULL (size);
  BTOR_ABORT_REFS_NOT_POS (e_array);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_array);
  BTOR_ABORT_IS_BV (e_array);

  fun_assignment (btor, e_array, indices, values, size, &ass);

  /* special case: we treat out parameters as return values for btoruntrace */
  BTOR_TRAPI_RETURN ("%p %p %d", *indices, *values, *size);

#ifndef NDEBUG
  if (btor->clone)
  {
    char **cindices, **cvalues;
    int i, csize;
    boolector_array_assignment (
        btor->clone, BTOR_CLONED_EXP (e_array), &cindices, &cvalues, &csize);
    assert (csize == *size);
    for (i = 0; i < *size; i++)
    {
      assert (!strcmp ((*indices)[i], cindices[i]));
      assert (!strcmp ((*values)[i], cvalues[i]));
    }
    if (ass)
    {
      assert (*size);
      ass->cloned_indices = cindices;
      ass->cloned_values  = cvalues;
    }
    btor_chkclone (btor, btor->clone);
  }
#endif
}

void
boolector_free_array_assignment (Btor *btor,
                                 char **indices,
                                 char **values,
                                 int size)
{
  BtorFunAss *funass;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%p %p %d", indices, values, size);
  BTOR_ABORT (size < 0, "negative size");
  BTOR_ABORT (size && !indices, "size > 0 but 'indices' are zero");
  BTOR_ABORT (size && !values, "size > 0 but 'values' are zero");
  BTOR_ABORT (!size && indices, "non zero 'indices' but 'size == 0'");
  BTOR_ABORT (!size && values, "non zero 'values' but 'size == 0'");
  funass =
      btor_ass_get_fun ((const char **) indices, (const char **) values, size);
  (void) funass;
#ifndef NDEBUG
  char **cindices, **cvalues;
  cindices = funass->cloned_indices;
  cvalues  = funass->cloned_values;
#endif
  btor_ass_release_fun (btor->fun_assignments, indices, values, size);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (free_array_assignment, cindices, cvalues, size);
#endif
}

void
boolector_uf_assignment (
    Btor *btor, BoolectorNode *n_uf, char ***args, char ***values, int *size)
{
  BtorNode *e_uf;
  BtorFunAss *ass;

  e_uf = BTOR_IMPORT_BOOLECTOR_NODE (n_uf);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (btor->last_sat_result != BTOR_RESULT_SAT,
              "cannot retrieve model if input formula is not SAT");
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN),
              "model generation has not been enabled");
  BTOR_ABORT_ARG_NULL (e_uf);
  BTOR_TRAPI_UNFUN (e_uf);
  BTOR_ABORT_ARG_NULL (args);
  BTOR_ABORT_ARG_NULL (values);
  BTOR_ABORT_ARG_NULL (size);
  BTOR_ABORT_REFS_NOT_POS (e_uf);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_uf);
  BTOR_ABORT_IS_BV (e_uf);

  fun_assignment (btor, e_uf, args, values, size, &ass);

  /* special case: we treat out parameters as return values for btoruntrace */
  BTOR_TRAPI_RETURN ("%p %p %d", *args, *values, *size);

#ifndef NDEBUG
  if (btor->clone)
  {
    char **cargs, **cvalues;
    int i, csize;
    boolector_uf_assignment (
        btor->clone, BTOR_CLONED_EXP (e_uf), &cargs, &cvalues, &csize);
    assert (csize == *size);
    for (i = 0; i < *size; i++)
    {
      assert (!strcmp ((*args)[i], cargs[i]));
      assert (!strcmp ((*values)[i], cvalues[i]));
    }
    if (ass)
    {
      assert (*size);
      ass->cloned_indices = cargs;
      ass->cloned_values  = cvalues;
    }
    btor_chkclone (btor, btor->clone);
  }
#endif
}

void
boolector_free_uf_assignment (Btor *btor, char **args, char **values, int size)
{
  BtorFunAss *funass;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%p %p %d", args, values, size);
  BTOR_ABORT (size < 0, "negative size");
  BTOR_ABORT (size && !args, "size > 0 but 'args' are zero");
  BTOR_ABORT (size && !values, "size > 0 but 'values' are zero");
  BTOR_ABORT (!size && args, "non zero 'args' but 'size == 0'");
  BTOR_ABORT (!size && values, "non zero 'values' but 'size == 0'");
  funass =
      btor_ass_get_fun ((const char **) args, (const char **) values, size);
  (void) funass;
#ifndef NDEBUG
  char **cargs, **cvalues;
  cargs   = funass->cloned_indices;
  cvalues = funass->cloned_values;
#endif
  btor_ass_release_fun (btor->fun_assignments, args, values, size);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (free_array_assignment, cargs, cvalues, size);
#endif
}

void
boolector_print_model (Btor *btor, char *format, FILE *file)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (format);
  BTOR_TRAPI ("%s", format);
  BTOR_ABORT_ARG_NULL (file);
  BTOR_ABORT (strcmp (format, "btor") && strcmp (format, "smt2"),
              "invalid model output format: %s",
              format);
  BTOR_ABORT (btor->last_sat_result != BTOR_RESULT_SAT,
              "cannot retrieve model if input formula is not SAT");
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN),
              "model generation has not been enabled");
  btor_print_model (btor, format, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (print_model, format, file);
#endif
}

/*------------------------------------------------------------------------*/

BoolectorSort
boolector_bool_sort (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");

  BtorSortId res;
  res = btor_bool_sort (btor);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, bool_sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort
boolector_bitvec_sort (Btor *btor, int width)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d", width);
  BTOR_ABORT (width <= 0, "'width' must be > 0");

  BtorSortId res;
  res = btor_bitvec_sort (btor, width);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, bitvec_sort, width);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

static BtorSortId
boolector_tuple_sort (Btor *btor, BoolectorSort *sorts, size_t num_elements)
{
  BtorSortId element_ids[num_elements];
  size_t i;
  for (i = 0; i < num_elements; i++)
    element_ids[i] = BTOR_IMPORT_BOOLECTOR_SORT (sorts[i]);
  return btor_tuple_sort (btor, element_ids, num_elements);
}

BoolectorSort
boolector_fun_sort (Btor *btor,
                    BoolectorSort domain[],
                    int arity,
                    BoolectorSort codomain)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (domain);
  BTOR_ABORT (arity <= 0, "'arity' must be > 0");

  int i, len;
  BtorSortId res, tup, cos, s;
  char *strtrapi;

  len = 8 + 10 + (arity + 1) * 20;
  BTOR_NEWN (btor->mm, strtrapi, len);

  sprintf (strtrapi, SORT_FMT, BTOR_IMPORT_BOOLECTOR_SORT ((domain[0])), btor);
  for (i = 1; i < arity; i++)
    sprintf (strtrapi + strlen (strtrapi),
             SORT_FMT,
             BTOR_IMPORT_BOOLECTOR_SORT (domain[i]),
             btor);
  sprintf (strtrapi + strlen (strtrapi),
           SORT_FMT,
           BTOR_IMPORT_BOOLECTOR_SORT (codomain),
           btor);
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);

  for (i = 0; i < arity; i++)
  {
    s = BTOR_IMPORT_BOOLECTOR_SORT (domain[i]);
    BTOR_ABORT (!btor_is_valid_sort (btor, s),
                "'domain' sort at position %d is not a valid sort",
                i);
    BTOR_ABORT (
        !btor_is_bitvec_sort (btor, s) && !btor_is_bool_sort (btor, s),
        "'domain' sort at position %d must be a bool or bit vector sort",
        i);
  }
  cos = BTOR_IMPORT_BOOLECTOR_SORT (codomain);
  BTOR_ABORT (!btor_is_valid_sort (btor, cos),
              "'codomain' sort is not a valid sort");
  BTOR_ABORT (
      !btor_is_bitvec_sort (btor, cos) && !btor_is_bool_sort (btor, cos),
      "'codomain' sort must be a bool or bit vector sort");

  tup = boolector_tuple_sort (btor, domain, arity);

  res = btor_fun_sort (btor, tup, cos);
  btor_release_sort (btor, tup);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, fun_sort, domain, arity, codomain);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort
boolector_array_sort (Btor *btor, BoolectorSort index, BoolectorSort element)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (SORT_FMT " " SORT_FMT, index, btor, element, btor);

  BtorSortId is, es, res;

  is = BTOR_IMPORT_BOOLECTOR_SORT (index);
  es = BTOR_IMPORT_BOOLECTOR_SORT (element);

  BTOR_ABORT (!btor_is_valid_sort (btor, is),
              "'index' sort is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, is),
              "'index' is not a bit vector sort");
  BTOR_ABORT (!btor_is_valid_sort (btor, es),
              "'element' sort is not a valid sort");
  BTOR_ABORT (!btor_is_bitvec_sort (btor, es),
              "'element' is not a bit vector sort");

  res = btor_array_sort (btor, is, es);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, array_sort, index, element);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

void
boolector_release_sort (Btor *btor, BoolectorSort sort)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (SORT_FMT, BTOR_IMPORT_BOOLECTOR_SORT (sort), btor);

  BtorSortId s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");
  dec_sort_ext_ref_counter (btor, s);
  btor_release_sort (btor, s);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (release_sort, sort);
#endif
}

bool
boolector_is_equal_sort (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  bool res;
  BtorNode *e0, *e1;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e0);
  BTOR_ABORT_ARG_NULL (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS (e0);
  BTOR_ABORT_REFS_NOT_POS (e1);
  BTOR_ABORT_BTOR_MISMATCH (btor, e0);
  BTOR_ABORT_BTOR_MISMATCH (btor, e1);
  res = btor_exp_get_sort_id (e0) == btor_exp_get_sort_id (e1);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (
      res, is_equal_sort, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return res;
}

bool
boolector_is_array_sort (Btor *btor, BoolectorSort sort)
{
  bool res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);

  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");

  res = btor_is_array_sort (btor, s);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_array_sort, sort);
#endif
  return res;
}

bool
boolector_is_bitvec_sort (Btor *btor, BoolectorSort sort)
{
  bool res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);

  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");

  res = btor_is_bitvec_sort (btor, s);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_bitvec_sort, sort);
#endif
  return res;
}

bool
boolector_is_fun_sort (Btor *btor, BoolectorSort sort)
{
  bool res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);

  BTOR_ABORT (!btor_is_valid_sort (btor, s), "'sort' is not a valid sort");

  res = btor_is_fun_sort (btor, s);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_fun_sort, sort);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

/* Note: no need to trace parse function calls!! */

int
boolector_parse (Btor *btor,
                 FILE *infile,
                 const char *infile_name,
                 FILE *outfile,
                 char **error_msg,
                 int *status)
{
  int res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (infile);
  BTOR_ABORT_ARG_NULL (infile_name);
  BTOR_ABORT_ARG_NULL (outfile);
  BTOR_ABORT_ARG_NULL (error_msg);
  BTOR_ABORT_ARG_NULL (status);
  BTOR_ABORT (BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
              "file parsing must be done before creating expressions");
  res = btor_parse (btor, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

int
boolector_parse_btor (Btor *btor,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      int *status)
{
  int res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (infile);
  BTOR_ABORT_ARG_NULL (infile_name);
  BTOR_ABORT_ARG_NULL (outfile);
  BTOR_ABORT_ARG_NULL (error_msg);
  BTOR_ABORT_ARG_NULL (status);
  BTOR_ABORT (BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
              "file parsing must be done before creating expressions");
  res = btor_parse_btor (btor, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

int
boolector_parse_smt1 (Btor *btor,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      int *status)
{
  int res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (infile);
  BTOR_ABORT_ARG_NULL (infile_name);
  BTOR_ABORT_ARG_NULL (outfile);
  BTOR_ABORT_ARG_NULL (error_msg);
  BTOR_ABORT_ARG_NULL (status);
  BTOR_ABORT (BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
              "file parsing must be done before creating expressions");
  res = btor_parse_smt1 (btor, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

int
boolector_parse_smt2 (Btor *btor,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      int *status)
{
  int res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (infile);
  BTOR_ABORT_ARG_NULL (infile_name);
  BTOR_ABORT_ARG_NULL (outfile);
  BTOR_ABORT_ARG_NULL (error_msg);
  BTOR_ABORT_ARG_NULL (status);
  BTOR_ABORT (BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
              "file parsing must be done before creating expressions");
  res = btor_parse_smt2 (btor, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

/*------------------------------------------------------------------------*/

void
boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (file);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  btor_dump_btor_node (btor, file, btor_simplify_exp (btor, exp));
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor_node, stdout, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_dump_btor (Btor *btor, FILE *file)
{
  BTOR_TRAPI ("");
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (file);
  BTOR_ABORT (!btor_can_be_dumped (btor),
              "formula cannot be dumped in BTOR format as it does "
              "not support uninterpreted functions yet.");
  BTOR_WARN (btor->assumptions->count > 0,
             "dumping in incremental mode only captures the current state "
             "of the input formula without assumptions");
  btor_dump_btor (btor, file, 1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor, stdout);
#endif
}

#if 0
void
boolector_dump_btor2 (Btor * btor, FILE * file)
{
  BTOR_TRAPI ("");
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (file);
  btor_dump_btor (btor, file, 2);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor, file);
#endif
}
#endif

void
boolector_dump_smt2_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (file);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  btor_dump_smt2_node (btor, file, btor_simplify_exp (btor, exp), 0);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt2_node, stdout, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_dump_smt2 (Btor *btor, FILE *file)
{
  BTOR_TRAPI ("");
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (file);
  BTOR_WARN (btor->assumptions->count > 0,
             "dumping in incremental mode only captures the current state "
             "of the input formula without assumptions");
  btor_dump_smt2 (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt2, stdout);
#endif
}

void
boolector_dump_aiger_ascii (Btor *btor, FILE *file, bool merge_roots)
{
  BTOR_TRAPI ("%d", merge_roots);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (file);
  BTOR_ABORT (btor->lambdas->count > 0 || btor->ufs->count > 0,
              "dumping to ASCII AIGER is supported for QF_BV only");
  BTOR_WARN (btor->assumptions->count > 0,
             "dumping in incremental mode only captures the current state "
             "of the input formula without assumptions");
  btor_dump_aiger (btor, file, false, merge_roots);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_aiger_ascii, stdout, merge_roots);
#endif
}

void
boolector_dump_aiger_binary (Btor *btor, FILE *file, bool merge_roots)
{
  BTOR_TRAPI ("%d", merge_roots);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (file);
  BTOR_ABORT (btor->lambdas->count > 0 || btor->ufs->count > 0,
              "dumping to binary AIGER is supported for QF_BV only");
  BTOR_WARN (btor->assumptions->count > 0,
             "dumping in incremental mode only captures the current state "
             "of the input formula without assumptions");
  btor_dump_aiger (btor, file, true, merge_roots);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_aiger_binary, stdout, merge_roots);
#endif
}

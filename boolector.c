/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2013-2014 Aina Niemetz.
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
#include "btorconst.h"
#include "btorcore.h"
#include "btorexit.h"
#include "btoriter.h"
#include "btortrapi.h"
#include "btorutil.h"
#include "dumper/btordumpbtor.h"
#include "dumper/btordumpsmt.h"
#ifdef BTOR_ENABLE_CLONING
#include "btorclone.h"
#endif
#include "btorhash.h"
#include "btorparse.h"
#include "btorsat.h"
#include "btorsort.h"

/*------------------------------------------------------------------------*/

#include <limits.h>
#include <stdio.h>
#include <string.h>

/*------------------------------------------------------------------------*/

static void
inc_exp_ext_ref_counter (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *real_exp = BTOR_REAL_ADDR_NODE (exp);
  BTOR_ABORT_BOOLECTOR (real_exp->ext_refs == INT_MAX,
                        "Node reference counter overflow");
  real_exp->ext_refs += 1;
  btor->external_refs += 1;
}

static void
dec_exp_ext_ref_counter (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BTOR_REAL_ADDR_NODE (exp)->ext_refs -= 1;
  btor->external_refs -= 1;
}
static void
inc_sort_ext_ref_counter (Btor *btor, BtorSort *sort)
{
  assert (btor);
  assert (sort);

  BTOR_ABORT_BOOLECTOR (sort->ext_refs == INT_MAX,
                        "Node reference counter overflow");
  sort->ext_refs += 1;
  btor->external_refs += 1;
}

static void
dec_sort_ext_ref_counter (Btor *btor, BtorSort *sort)
{
  assert (btor);
  assert (sort);

  sort->ext_refs -= 1;
  btor->external_refs -= 1;
}

/*------------------------------------------------------------------------*/

void
boolector_chkclone (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
#ifndef BTOR_ENABLE_CLONING
  BTOR_ABORT_BOOLECTOR (1, "cloning requires lingeling as SAT solver");
#endif
#ifndef NDEBUG
  if (btor->clone) btor_delete_btor (btor->clone);
  btor->clone = btor; /* mark clone as going-to-be shadow clone */
#ifdef BTOR_ENABLE_CLONING
  btor->clone = btor_clone_btor (btor);
#endif
  assert (btor->clone->mm);
  assert (btor->clone->avmgr);
  btor_chkclone (btor);
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

#define BTOR_CLONED_SORT(sort)                                            \
  ((btor->clone ? BTOR_EXPORT_BOOLECTOR_SORT (BTOR_PEEK_STACK (           \
                      btor->clone->sorts_unique_table.id2sort, sort->id)) \
                : 0))
#else
#define BTOR_CLONED_EXP(exp) 0
#define BTOR_CLONED_SORT(sort) 0
#endif

/*------------------------------------------------------------------------*/

/* for internal use (parser), only */

void
boolector_set_btor_id (Btor *btor, BoolectorNode *node, int id)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d", id);
  BTOR_ABORT_BOOLECTOR (
      !btor_is_bv_var_exp (btor, exp) && !btor_is_uf_array_var_exp (btor, exp),
      "'exp' is neither BV/array variable nor UF");
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor_set_btor_id (btor, exp, id);
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

/*------------------------------------------------------------------------*/

Btor *
boolector_new (void)
{
  char *trname;
  Btor *btor;
  btor = btor_new_btor_no_init ();
  if ((trname = getenv ("BTORAPITRACE"))) btor_open_apitrace (btor, trname);
  BTOR_TRAPI ("");
  BTOR_TRAPI_RETURN_PTR (btor);
  btor_init_opts (btor);
  return btor;
}

Btor *
boolector_clone (Btor *btor)
{
  Btor *clone;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
#ifdef BTOR_ENABLE_CLONING
  clone = btor_clone_btor (btor);
#else
  BTOR_ABORT_BOOLECTOR (1, "cloning requires Lingeling as SAT solver");
  clone = 0;
#endif
  BTOR_TRAPI_RETURN_PTR (clone);
  return clone;
}

void
boolector_delete (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  if (btor->close_apitrace == 1)
    fclose (btor->apitrace);
  else if (btor->close_apitrace == 2)
    pclose (btor->apitrace);
  if (btor->clone) boolector_delete (btor->clone);
  btor_delete_btor (btor);
}

void
boolector_set_msg_prefix (Btor *btor, const char *prefix)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  btor_reset_time_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_time);
#endif
}

void
boolector_reset_stats (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  btor_reset_stats_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_stats);
#endif
}

void
boolector_print_stats (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  btor_print_stats_sat (btor_get_sat_mgr_btor (btor));
  btor_print_stats_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (print_stats);
#endif
}

void
boolector_set_trapi (Btor *btor, FILE *apitrace)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (btor->apitrace, "API trace already set");
  btor->apitrace = apitrace;
}

FILE *
boolector_get_trapi (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  return btor->apitrace;
}

/*------------------------------------------------------------------------*/

void
boolector_assert (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp)->len != 1,
                        "'exp' must have bit-width one");
  btor_assert_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (assert, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_assume (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_BOOLECTOR (!btor->options.incremental.val,
                        "incremental usage has not been enabled");
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  /* Note: do not simplify constraint expression in order to prevent
   *       constraint expressions from not being added to btor->assumptions. */
  simp = BTOR_REAL_ADDR_NODE (exp)->simplified ? btor_simplify_exp (btor, exp)
                                               : exp;
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp)->len != 1,
                        "'exp' must have bit-width one");
  btor_assume_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (assume, BTOR_CLONED_EXP (exp));
#endif
}

int
boolector_failed (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_UNSAT,
      "cannot check failed assumptions if input formula is not UNSAT");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_BOOLECTOR (!btor->options.incremental.val,
                        "incremental usage has not been enabled");
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  /* Note: do not simplify expression (see boolector_assume). */
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (exp)->len != 1,
                        "'exp' must have bit-width one");
  BTOR_ABORT_BOOLECTOR (!btor_is_assumption_exp (btor, exp),
                        "'exp' must be an assumption");
  res = btor_failed_exp (btor, exp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, failed, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_sat (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT_BOOLECTOR (
      !btor->options.incremental.val && btor->btor_sat_btor_called > 0,
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
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%d %d", lod_limit, sat_limit);
  BTOR_ABORT_BOOLECTOR (
      !btor->options.incremental.val && btor->btor_sat_btor_called > 0,
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

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%s", solver);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (solver);
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  res = btor_set_sat_solver (btor_get_sat_mgr_btor (btor), solver, 0, 0);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, set_sat_solver, solver);
#endif
  return res;
}

#ifdef BTOR_USE_LINGELING
int
boolector_set_sat_solver_lingeling (Btor *btor, const char *optstr, int nofork)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%s %d", optstr, nofork);
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  res = btor_set_sat_solver (
      btor_get_sat_mgr_btor (btor), "lingeling", optstr, nofork);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, set_sat_solver_lingeling, optstr, nofork);
#endif
  return res;
}
#endif

#ifdef BTOR_USE_PICOSAT
int
boolector_set_sat_solver_picosat (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  res = btor_set_sat_solver (btor_get_sat_mgr_btor (btor), "picosat", 0, 0);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, set_sat_solver_picosat);
#endif
  return res;
}
#endif

#ifdef BTOR_USE_MINISAT
int
boolector_set_sat_solver_minisat (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  res = btor_set_sat_solver (btor_get_sat_mgr_btor (btor), "minisat", 0, 0);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, set_sat_solver_minisat);
#endif
  return res;
}
#endif

/*------------------------------------------------------------------------*/

void
boolector_set_opt (Btor *btor, const char *opt, int val)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%s %d", opt, val);
  BTOR_ABORT_BOOLECTOR (!btor_get_opt (btor, opt), "invalid option '%s'", opt);

  if (!strcmp (opt, BTOR_OPT_INCREMENTAL))
  {
    BTOR_ABORT_BOOLECTOR (val == 0,
                          "disabling incremental usage is not allowed");
    BTOR_ABORT_BOOLECTOR (btor->btor_sat_btor_called > 0,
                          "enabling incremental usage must be done before "
                          "calling 'boolector_sat'");
  }
#ifdef BTOR_ENABLE_DUAL_PROPAGATION
  else if (!strcmp (opt, BTOR_OPT_DUAL_PROP))
  {
    BTOR_ABORT_BOOLECTOR (
        val && btor->options.just.val,
        "enabling multiple optimization techniques is not allowed");
  }
#endif
  else if (!strcmp (opt, BTOR_OPT_JUST))
  {
#ifdef BTOR_ENABLE_DUAL_PROPAGATION
    BTOR_ABORT_BOOLECTOR (
        val && btor->options.dual_prop.val,
        "enabling multiple optimization techniques is not allowed");
#endif
  }
#ifdef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  else if (!strcmp (opt, BTOR_OPT_UCOPT))
  {
    return;
  }
#endif
  else if (!strcmp (opt, BTOR_OPT_REWRITE_LEVEL))
  {
    BTOR_ABORT_BOOLECTOR (val < 0 || val > 3,
                          "'rewrite_level' must be in [0,3]");
    BTOR_ABORT_BOOLECTOR (
        BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
        "setting rewrite level must be done before creating expressions");
  }
  else if (!strcmp (opt, BTOR_OPT_REWRITE_LEVEL_PBR))
  {
    BTOR_ABORT_BOOLECTOR (val < 0 || val > 3,
                          "'rewrite_level_pbr' must be in [0,3]");
  }
#ifdef NBTORLOG
  else if (!strcmp (opt, BTOR_OPT_LOGLEVEL))
  {
    return;
  }
#endif

  btor_set_opt (btor, opt, val);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_opt, opt, val);
#endif
}

const BtorOpt *
boolector_get_opt (Btor *btor, const char *opt)
{
  BtorOpt *res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%s", opt);
  /* Note: we can't use btor_get_opt here (asserts that option with given
   * name indeed exists) but want to issue an abort if necessary */
  res = btor_get_opt_aux (btor, opt);
  BTOR_ABORT_BOOLECTOR (res == 0, "invalid option '%s'", opt);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_OPT (res, get_opt, opt);
#endif
  return res;
}

int
boolector_get_opt_val (Btor *btor, const char *opt)
{
  int res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%s", opt);
  BTOR_ABORT_BOOLECTOR (
      btor_get_opt_aux (btor, opt) == 0, "invalid option '%s'", opt);
  res = btor_get_opt_val (btor, opt);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_opt_val, opt);
#endif
  return res;
}

const BtorOpt *
boolector_first_opt (Btor *btor)
{
  BtorOpt *res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  res = btor_first_opt (btor);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_OPT (res, first_opt);
#endif
  return res;
}

const BtorOpt *
boolector_last_opt (Btor *btor)
{
  BtorOpt *res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  res = btor_last_opt (btor);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_OPT (res, last_opt);
#endif
  return res;
}

const BtorOpt *
boolector_next_opt (Btor *btor, const BtorOpt *opt)
{
  BtorOpt *res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (opt);
  BTOR_TRAPI ("%p", opt);
  res = btor_next_opt (btor, opt);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_OPT (res, next_opt, opt);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_copy (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  res = btor_copy_exp (btor, exp);
  inc_exp_ext_ref_counter (btor, res);
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
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
#ifndef NDEBUG
  BoolectorNode *cexp = BTOR_CLONED_EXP (exp);
#endif
  assert (BTOR_REAL_ADDR_NODE (exp)->ext_refs);
  dec_exp_ext_ref_counter (btor, exp);
  btor_release_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (release, cexp);
#endif
}

void
boolector_release_all (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%s", bits);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (bits);
  BTOR_ABORT_BOOLECTOR (*bits == '\0', "'bits' must not be empty");
  res = btor_const_exp (btor, bits);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, const, bits);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_zero (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  res = btor_zero_exp (btor, width);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, zero, width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_false (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  res = btor_false_exp (btor);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, false);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ones (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  res = btor_ones_exp (btor, width);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ones, width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_true (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");
  res = btor_true_exp (btor);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, true);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_one (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  res = btor_one_exp (btor, width);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, one, width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_unsigned_int (Btor *btor, unsigned int u, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%u %d", u, width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  res = btor_unsigned_exp (btor, u, width);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, unsigned_int, u, width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_int (Btor *btor, int i, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%d %u", i, width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  res = btor_int_exp (btor, i, width);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, int, i, width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_var (Btor *btor, int width, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  BtorNode *res;
  char *symb;

  symb = (char *) symbol;
  BTOR_TRAPI ("%d %s", width, symb);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  BTOR_ABORT_BOOLECTOR (
      symb && btor_find_in_ptr_hash_table (btor->symbols, (char *) symb),
      "symbol '%s' is already in use",
      symb);
  res = btor_var_exp (btor, width, symb);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
  (void) btor_insert_in_ptr_hash_table (btor->inputs,
                                        btor_copy_exp (btor, res));
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, var, width, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_array (Btor *btor,
                 int elem_width,
                 int index_width,
                 const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  BtorNode *res;
  char *symb;

  symb = (char *) symbol;
  BTOR_TRAPI ("%d %d %s", elem_width, index_width, symb);
  BTOR_ABORT_BOOLECTOR (elem_width < 1, "'elem_width' must not be < 1");
  BTOR_ABORT_BOOLECTOR (index_width < 1, "'index_width' must not be < 1");
  BTOR_ABORT_BOOLECTOR (
      symb && btor_find_in_ptr_hash_table (btor->symbols, symb),
      "symbol '%s' is already in use",
      symb);
  res = btor_array_exp (btor, elem_width, index_width, symb);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
  (void) btor_insert_in_ptr_hash_table (btor->inputs,
                                        btor_copy_exp (btor, res));
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, array, elem_width, index_width, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uf (Btor *btor, BoolectorSort *sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (sort);

  BtorNode *res;
  BtorSort *s;
  char *symb;

  symb = (char *) symbol;
  s    = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_TRAPI (SORT_FMT "%s", BTOR_TRAPI_SORT_ID (s), symb);
  BTOR_ABORT_BOOLECTOR (s->table != &btor->sorts_unique_table,
                        "%ssort%s%s%s%s does not belong to 'btor'",
                        symbol ? "" : "'",
                        symbol ? "" : "'",
                        symbol ? " '" : "",
                        symbol ? symbol : "",
                        symbol ? "'" : "");
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_FUN_SORT (BTOR_IMPORT_BOOLECTOR_SORT (sort)),
                        "%ssort%s%s%s%s must be a function sort",
                        symbol ? "" : "'",
                        symbol ? "" : "'",
                        symbol ? " '" : "",
                        symbol ? symbol : "",
                        symbol ? "'" : "");
  BTOR_ABORT_BOOLECTOR (
      symb && btor_find_in_ptr_hash_table (btor->symbols, symb),
      "symbol '%s' is already in use",
      symb);

  res = btor_uf_exp (btor, BTOR_IMPORT_BOOLECTOR_SORT (sort), symb);
  assert (BTOR_IS_REGULAR_NODE (res));
  inc_exp_ext_ref_counter (btor, res);
  (void) btor_insert_in_ptr_hash_table (btor->inputs,
                                        btor_copy_exp (btor, res));
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, uf, BTOR_CLONED_SORT (BTOR_IMPORT_BOOLECTOR_SORT (sort)), symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_not (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  res = btor_not_exp (btor, simp);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, not, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_neg (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  res = btor_neg_exp (btor, simp);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, neg, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redor (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  res = btor_redor_exp (btor, simp);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redor, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redxor (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  res = btor_redxor_exp (btor, simp);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redxor, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redand (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  res = btor_redand_exp (btor, simp);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redand, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slice (Btor *btor, BoolectorNode *node, int upper, int lower)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d %d", upper, lower);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (lower < 0, "'lower' must not be negative");
  BTOR_ABORT_BOOLECTOR (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT_BOOLECTOR (upper >= BTOR_REAL_ADDR_NODE (simp)->len,
                        "'upper' must not be >= width of 'exp'");
  res = btor_slice_exp (btor, simp, upper, lower);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slice, BTOR_CLONED_EXP (exp), upper, lower);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uext (Btor *btor, BoolectorNode *node, int width)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d", width);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  res = btor_uext_exp (btor, simp, width);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, uext, BTOR_CLONED_EXP (exp), width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sext (Btor *btor, BoolectorNode *node, int width)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d", width);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  res = btor_sext_exp (btor, simp, width);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sext, BTOR_CLONED_EXP (exp), width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_implies (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp0)->len != 1
                            || BTOR_REAL_ADDR_NODE (simp1)->len != 1,
                        "bit-width of 'e0' and 'e1' have be 1");
  res = btor_implies_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp0)->len != 1
                            || BTOR_REAL_ADDR_NODE (simp1)->len != 1,
                        "bit-width of 'e0' and 'e1' must not be unequal to 1");
  res = btor_iff_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, iff, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_xor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_xor_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, xor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_xnor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_xnor_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, xnor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_and (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_and_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, and, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_nand (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_nand_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nand, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_or (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_or_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, or, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_nor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_nor_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_eq (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (!btor_equal_sort (btor, e0, e1),
                        "nodes must have equal sorts");
  res = btor_eq_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, eq, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ne (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *real_simp0, *real_simp1, *res;
  int is_array_simp0, is_array_simp1;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0          = btor_simplify_exp (btor, e0);
  simp1          = btor_simplify_exp (btor, e1);
  real_simp0     = BTOR_REAL_ADDR_NODE (simp0);
  real_simp1     = BTOR_REAL_ADDR_NODE (simp1);
  is_array_simp0 = BTOR_IS_FUN_NODE (real_simp0);
  is_array_simp1 = BTOR_IS_FUN_NODE (real_simp1);
  BTOR_ABORT_BOOLECTOR (is_array_simp0 != is_array_simp1,
                        "array must not be compared to bit-vector");
  BTOR_ABORT_BOOLECTOR (is_array_simp0 && real_simp0->len != real_simp1->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp0
                            && BTOR_ARRAY_INDEX_LEN (real_simp0)
                                   != BTOR_ARRAY_INDEX_LEN (real_simp1),
                        "arrays must not have unequal index bit-width");
  res = btor_ne_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ne, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_add (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_add_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, add, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uaddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_uaddo_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_saddo_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_mul_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, mul, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_umulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_umulo_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_smulo_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_ult_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ult, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_slt_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ulte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_ulte_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ulte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_slte_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ugt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_ugt_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ugt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sgt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_sgt_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sgt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ugte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_ugte_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ugte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sgte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_sgte_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_sll_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_srl_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_sra_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_rol_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_ror_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ror, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sub (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_sub_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sub, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_usubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_usubo_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_ssubo_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_udiv_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, udiv, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sdiv (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_sdiv_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sdiv, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sdivo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_sdivo_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_urem_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, urem, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_srem (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_srem_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, srem, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_smod (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  res = btor_smod_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, smod, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_concat (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN (e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (e0)->len
                            > INT_MAX - BTOR_REAL_ADDR_NODE (simp1)->len,
                        "bit-width of result is too large");
  res = btor_concat_exp (btor, simp0, simp1);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e_array, *e_index, *simp_array, *simp_index, *res;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  e_index = BTOR_IMPORT_BOOLECTOR_NODE (n_index);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_index);
  BTOR_TRAPI_BINFUN (e_array, e_index);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_index);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_index);
  simp_array = btor_simplify_exp (btor, e_array);
  simp_index = btor_simplify_exp (btor, e_index);
  BTOR_ABORT_BV_BOOLECTOR (simp_array);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp_index);
  BTOR_ABORT_BOOLECTOR (
      BTOR_ARRAY_INDEX_LEN (simp_array)
          != BTOR_REAL_ADDR_NODE (simp_index)->len,
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  res = btor_read_exp (btor, simp_array, simp_index);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *e_array, *e_index, *e_value, *simp_array, *simp_index, *simp_value;
  BtorNode *res;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  e_index = BTOR_IMPORT_BOOLECTOR_NODE (n_index);
  e_value = BTOR_IMPORT_BOOLECTOR_NODE (n_value);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_index);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_value);
  BTOR_TRAPI_TERFUN (e_array, e_index, e_value);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_index);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_value);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_index);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_value);
  simp_array = btor_simplify_exp (btor, e_array);
  simp_index = btor_simplify_exp (btor, e_index);
  simp_value = btor_simplify_exp (btor, e_value);
  BTOR_ABORT_BV_BOOLECTOR (simp_array);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp_index);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp_value);
  BTOR_ABORT_BOOLECTOR (
      BTOR_ARRAY_INDEX_LEN (simp_array)
          != BTOR_REAL_ADDR_NODE (simp_index)->len,
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  BTOR_ABORT_BOOLECTOR (
      simp_array->len != BTOR_REAL_ADDR_NODE (simp_value)->len,
      "element bit-width of 'e_array' and bit-width of 'e_value' must be "
      "equal");
  res = btor_write_exp (btor, simp_array, simp_index, simp_value);
  inc_exp_ext_ref_counter (btor, res);
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
                BoolectorNode *n_if,
                BoolectorNode *n_else)
{
  BtorNode *e_cond, *e_if, *e_else;
  BtorNode *simp_cond, *simp_if, *simp_else, *real_simp_if, *real_simp_else;
  BtorNode *res;
  int is_array_simp_if, is_array_simp_else;

  e_cond = BTOR_IMPORT_BOOLECTOR_NODE (n_cond);
  e_if   = BTOR_IMPORT_BOOLECTOR_NODE (n_if);
  e_else = BTOR_IMPORT_BOOLECTOR_NODE (n_else);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_cond);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_if);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_else);
  BTOR_TRAPI_TERFUN (e_cond, e_if, e_else);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_cond);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_if);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_else);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_cond);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_if);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_else);
  simp_cond = btor_simplify_exp (btor, e_cond);
  simp_if   = btor_simplify_exp (btor, e_if);
  simp_else = btor_simplify_exp (btor, e_else);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp_cond);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp_cond)->len != 1,
                        "bit-width of 'e_cond' must be equal to 1");
  real_simp_if       = BTOR_REAL_ADDR_NODE (simp_if);
  real_simp_else     = BTOR_REAL_ADDR_NODE (simp_else);
  is_array_simp_if   = BTOR_IS_FUN_NODE (real_simp_if);
  is_array_simp_else = BTOR_IS_FUN_NODE (real_simp_else);
  BTOR_ABORT_BOOLECTOR (is_array_simp_if != is_array_simp_else,
                        "array must not be combined with bit-vector");
  BTOR_ABORT_BOOLECTOR (!is_array_simp_if && real_simp_if && real_simp_else
                            && real_simp_if->len != real_simp_else->len,
                        "bit-vectors must not have unequal bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp_if && real_simp_if && real_simp_else
                            && real_simp_if->len != real_simp_else->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp_if && real_simp_if && real_simp_else
                            && BTOR_ARRAY_INDEX_LEN (real_simp_if)
                                   != BTOR_ARRAY_INDEX_LEN (real_simp_else),
                        "arrays must not have unequal index bit-width");
  res = btor_cond_exp (btor, simp_cond, simp_if, simp_else);
  inc_exp_ext_ref_counter (btor, res);
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
boolector_param (Btor *btor, int width, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  BtorNode *res;
  char *symb;

  symb = (char *) symbol;
  BTOR_TRAPI ("%d %s", width, symb);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  BTOR_ABORT_BOOLECTOR (
      symb && btor_find_in_ptr_hash_table (btor->symbols, symb),
      "symbol '%s' is already in use",
      symb);
  res = btor_param_exp (btor, width, symb);
  inc_exp_ext_ref_counter (btor, res);

  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, param, width, symbol);
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

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (params);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  BTOR_ABORT_BOOLECTOR (paramc < 1, "'paramc' must not be < 1");

  len = 5 + 10 + paramc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "%d ", paramc);

  for (i = 0; i < paramc; i++)
  {
    BTOR_ABORT_BOOLECTOR (
        !params[i] || !BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (params[i])),
        "'params[%d]' is not a parameter",
        i);
    BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (params[i]);
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (params[i]));
  }
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (exp));
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  res = btor_fun_exp (btor, paramc, params, exp);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode **args, *e_fun, *res, *cur;

  args  = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);
  e_fun = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_fun);

  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (n_fun);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, n_fun);

  len = 7 + 10 + argc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "%d ", argc);

  cur = BTOR_REAL_ADDR_NODE (btor_simplify_exp (btor, e_fun));
  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_BOOLECTOR (
        !BTOR_IS_UF_NODE (cur) && !BTOR_IS_LAMBDA_NODE (cur),
        "number of arguments must be <= number of parameters in 'fun'");
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
    if (!BTOR_IS_UF_NODE (cur))
      cur = BTOR_REAL_ADDR_NODE (btor_simplify_exp (btor, cur->e[1]));
  }
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (e_fun));

  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);

  e_fun = btor_simplify_exp (btor, e_fun);
  BTOR_ABORT_BOOLECTOR (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT_BOOLECTOR (argc >= 1 && !args,
                        "no arguments given but argc defined > 0");
  BTOR_ABORT_BOOLECTOR (!btor_is_fun_exp (btor, e_fun)
                            || argc != btor_get_fun_arity (btor, e_fun),
                        "number of arguments does not match arity of 'fun'");
  i = btor_fun_sort_check (btor, argc, args, e_fun);
  BTOR_ABORT_BOOLECTOR (i >= 0,
                        "sort of argument at position %d does not match given"
                        " function signature",
                        i);
  res = btor_apply_exps (btor, argc, args, e_fun);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);

  res = btor_inc_exp (btor, simp);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, inc, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_dec (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);

  res = btor_dec_exp (btor, simp);
  inc_exp_ext_ref_counter (btor, res);
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
  BtorNode *exp, *real_exp, *simp, *real_simp;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  real_exp = BTOR_REAL_ADDR_NODE (exp);
  btor     = real_exp->btor;
  BTOR_TRAPI_UNFUN (exp);
  simp      = btor_simplify_exp (real_exp->btor, exp);
  real_simp = BTOR_REAL_ADDR_NODE (simp);
  assert (btor == real_simp->btor);
  assert (real_simp->btor == real_exp->btor);
  BTOR_TRAPI_RETURN_PTR (btor);
#ifndef NDEBUG
  if (btor->clone)
  {
    Btor *clone = boolector_get_btor (BTOR_CLONED_EXP (exp));
    assert (clone == btor->clone);
    btor_chkclone (btor);
  }
#else
  (void) real_simp;
#endif
  return btor;
}

int
boolector_get_id (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (node);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  res = btor_get_id (btor, exp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_id, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

BoolectorNode *
boolector_match_node_by_id (Btor *btor, int id)
{
  BtorNode *res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (id <= 0, "node id must be > 0");
  BTOR_TRAPI ("%d", id);
  res = btor_match_node_by_id (btor, id);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, match_node_by_id, id);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_match_node (Btor *btor, BoolectorNode *node)
{
  BtorNode *res, *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  res = btor_match_node (btor, exp);
  inc_exp_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, match_node, node);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

const char *
boolector_get_symbol (Btor *btor, BoolectorNode *node)
{
  const char *res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
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
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (symbol);
  BTOR_TRAPI_UNFUN_EXT (exp, "%s", symbol);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor_set_symbol_exp (btor, exp, symbol);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_symbol, BTOR_CLONED_EXP (exp), symbol);
#endif
}

int
boolector_get_width (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  res = btor_get_exp_len (btor, exp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_width, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_get_index_width (Btor *btor, BoolectorNode *n_array)
{
  int res;
  BtorNode *e_array, *simp_array;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_TRAPI_UNFUN (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  simp_array = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (simp_array);
  res = btor_get_index_exp_len (btor, simp_array);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_index_width, BTOR_CLONED_EXP (e_array));
#endif
  return res;
}

const char *
boolector_get_bits (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *real;
  const char *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (node);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  real = BTOR_REAL_ADDR_NODE (simp);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_BV_CONST_NODE (real),
                        "argument is not a constant node");
  if (BTOR_IS_INVERTED_NODE (simp))
  {
    if (!real->invbits)
      real->invbits = btor_not_const_3vl (btor->mm, real->bits);
    res = real->invbits;
  }
  else
    res = simp->bits;
  BTOR_TRAPI_RETURN_STR (res);
#ifndef NDEBUG
  if (btor->clone)
  {
    const char *cloned_res =
        boolector_get_bits (btor->clone, BTOR_CLONED_EXP (node));
    assert (!strcmp (cloned_res, res));
  }
#endif
  return res;
}

int
boolector_get_fun_arity (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (!btor_is_fun_exp (btor, simp),
                        "given expression is not a function node");
  res = btor_get_fun_arity (btor, simp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_fun_arity, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_is_const (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *real;
  int res;
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  simp = btor_simplify_exp (btor, exp);
  real = BTOR_REAL_ADDR_NODE (simp);
  res  = BTOR_IS_BV_CONST_NODE (real);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_const, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_is_var (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *real;
  int res;
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  real = BTOR_REAL_ADDR_NODE (simp);
  res  = btor_is_bv_var_exp (btor, real);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_const, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_is_array (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_array_exp (btor, simp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_array, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_is_array_var (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_uf_array_var_exp (btor, simp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_array_var, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_is_param (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;
  int res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_param_exp (btor, simp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_param, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_is_bound_param (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;
  int res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (simp)),
                        "given expression is not a parameter node");
  res = btor_is_bound_param_exp (btor, simp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_bound_param, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_is_fun (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_fun_exp (btor, simp);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_fun, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

int
boolector_fun_sort_check (Btor *btor,
                          BoolectorNode **arg_nodes,
                          int argc,
                          BoolectorNode *n_fun)
{
  BtorNode **args, *e_fun, *simp;
  char *strtrapi;
  int i, len, res;

  args  = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);
  e_fun = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_fun);
  BTOR_ABORT_BOOLECTOR (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT_BOOLECTOR (argc >= 1 && !args,
                        "no arguments given but argc defined > 0");

  len = 15 + 10 + argc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "%d", argc);

  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_ARG_NULL_BOOLECTOR (args[i]);
    BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (args[i]);
    BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, args[i]);
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
  }
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (e_fun));
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  simp = btor_simplify_exp (btor, e_fun);
  res  = btor_fun_sort_check (btor, argc, args, simp);
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
  const char *ass;
  const char *res;
  BtorNode *exp, *simp;
  BtorBVAssignment *bvass;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_SAT,
      "cannot retrieve assignment if input formula is not SAT");
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (!btor->options.model_gen.val,
                        "model generation has not been enabled");
  ass   = btor_bv_assignment_str (btor, simp);
  bvass = btor_new_bv_assignment (btor->bv_assignments, (char *) ass);
  btor_release_bv_assignment_str (btor, (char *) ass);
  res = btor_get_bv_assignment_str (bvass);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  if (btor->clone)
  {
    const char *cloneres =
        boolector_bv_assignment (btor->clone, BTOR_CLONED_EXP (exp));
    assert (!strcmp (cloneres, res));
    bvass->cloned_assignment = cloneres;
    btor_chkclone (btor);
  }
#endif
  return res;
}

void
boolector_free_bv_assignment (Btor *btor, const char *assignment)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%p", assignment);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (assignment);
#ifndef NDEBUG
  char *cass;
  cass = (char *) btor_get_bv_assignment ((const char *) assignment)
             ->cloned_assignment;
#endif
  btor_release_bv_assignment (btor->bv_assignments, assignment);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (free_bv_assignment, cass);
#endif
}

void
boolector_array_assignment (Btor *btor,
                            BoolectorNode *n_array,
                            char ***indices,
                            char ***values,
                            int *size)
{
  int i;
  char **ind, **val;
  BtorNode *e_array, *simp;
  BtorArrayAssignment *arrass;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_SAT,
      "cannot retrieve assignment if input formula is not SAT");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_TRAPI_UNFUN (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (indices);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (values);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (size);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  simp = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (!btor->options.model_gen.val,
                        "model generation has not been enabled");

  btor_array_assignment_str (btor, simp, &ind, &val, size);

  if (*size)
  {
    arrass =
        btor_new_array_assignment (btor->array_assignments, ind, val, *size);
    for (i = 0; i < *size; i++)
    {
      btor_release_bv_assignment_str (btor, ind[i]);
      btor_release_bv_assignment_str (btor, val[i]);
    }
    btor_free (btor->mm, ind, *size * sizeof (*ind));
    btor_free (btor->mm, val, *size * sizeof (*val));
    btor_get_array_assignment_indices_values (arrass, indices, values, *size);
  }
  else
    arrass = 0;  // remove warning

  /* special case: we treat out parameters as return values for btoruntrace */
  BTOR_TRAPI_RETURN ("%p %p %d", *indices, *values, *size);

#ifndef NDEBUG
  if (btor->clone)
  {
    char **cindices, **cvalues;
    int csize;

    boolector_array_assignment (
        btor->clone, BTOR_CLONED_EXP (e_array), &cindices, &cvalues, &csize);
    assert (csize == *size);
    for (i = 0; i < *size; i++)
    {
      assert (!strcmp ((*indices)[i], cindices[i]));
      assert (!strcmp ((*values)[i], cvalues[i]));
    }
    if (arrass)
    {
      assert (*size);
      arrass->cloned_indices = cindices;
      arrass->cloned_values  = cvalues;
    }
    btor_chkclone (btor);
  }
#endif
}

void
boolector_free_array_assignment (Btor *btor,
                                 char **indices,
                                 char **values,
                                 int size)
{
  BtorArrayAssignment *arrass;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%p %p %d", indices, values, size);
  BTOR_ABORT_BOOLECTOR (size < 0, "negative size");
  if (size)
  {
    BTOR_ABORT_ARG_NULL_BOOLECTOR (indices);
    BTOR_ABORT_ARG_NULL_BOOLECTOR (values);
  }
  else
  {
    BTOR_ABORT_BOOLECTOR (indices, "non zero 'indices' but 'size == 0'");
    BTOR_ABORT_BOOLECTOR (values, "non zero 'values' but 'size == 0'");
  }
  arrass = btor_get_array_assignment (
      (const char **) indices, (const char **) values, size);
  (void) arrass;
#ifndef NDEBUG
  char **cindices, **cvalues;
  cindices = arrass->cloned_indices;
  cvalues  = arrass->cloned_values;
#endif
  btor_release_array_assignment (
      btor->array_assignments, indices, values, size);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (free_array_assignment, cindices, cvalues, size);
#endif
}

void
boolector_print_model (Btor *btor, FILE *file)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_TRAPI ("");
  btor_print_model (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (print_model, file);
#endif
}

/*------------------------------------------------------------------------*/

BoolectorSort *
boolector_bool_sort (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("");

  BtorSort *res;
  res = btor_bool_sort (&btor->sorts_unique_table);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, bool_sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort *
boolector_bitvec_sort (Btor *btor, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("%d", width);
  BTOR_ABORT_BOOLECTOR (width <= 0, "'width' must be > 0");

  BtorSort *res;
  res = btor_bitvec_sort (&btor->sorts_unique_table, width);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, bitvec_sort, width);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort *
boolector_array_sort (Btor *btor, BoolectorSort *index, BoolectorSort *elem)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI (SORT_FMT SORT_FMT,
              BTOR_TRAPI_SORT_ID (BTOR_IMPORT_BOOLECTOR_SORT (index)),
              BTOR_TRAPI_SORT_ID (BTOR_IMPORT_BOOLECTOR_SORT (elem)));
  BTOR_ABORT_ARG_NULL_BOOLECTOR (index);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (elem);
  BTOR_ABORT_BOOLECTOR (
      !BTOR_IS_BITVEC_SORT (BTOR_IMPORT_BOOLECTOR_SORT (index))
          && !BTOR_IS_BOOL_SORT (BTOR_IMPORT_BOOLECTOR_SORT (index)),
      "'index' sort must be a bool or bit vector sort");
  BTOR_ABORT_BOOLECTOR (
      !BTOR_IS_BITVEC_SORT (BTOR_IMPORT_BOOLECTOR_SORT (elem))
          && !BTOR_IS_BOOL_SORT (BTOR_IMPORT_BOOLECTOR_SORT (elem)),
      "'elem' sort must be a bool or bit vector sort");

  BtorSort *res, *i, *e;
  i   = BTOR_IMPORT_BOOLECTOR_SORT (index);
  e   = BTOR_IMPORT_BOOLECTOR_SORT (elem);
  res = btor_array_sort (&btor->sorts_unique_table, i, e);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (
      res, array_sort, BTOR_CLONED_SORT (i), BTOR_CLONED_SORT (e));
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort *
boolector_fun_sort (Btor *btor,
                    BoolectorSort **domain,
                    int arity,
                    BoolectorSort *codomain)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (domain);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (codomain);
  BTOR_ABORT_BOOLECTOR (arity <= 0, "'arity' must be > 0");

  int i, len;
  BtorSort *res;
  char *strtrapi;

  len = 8 + 10 + (arity + 1) * 20;
  BTOR_NEWN (btor->mm, strtrapi, len);

  sprintf (strtrapi,
           SORT_FMT,
           BTOR_TRAPI_SORT_ID (BTOR_IMPORT_BOOLECTOR_SORT ((domain[0]))));
  for (i = 1; i < arity; i++)
    sprintf (strtrapi + strlen (strtrapi),
             SORT_FMT,
             BTOR_TRAPI_SORT_ID (BTOR_IMPORT_BOOLECTOR_SORT (domain[i])));
  sprintf (strtrapi + strlen (strtrapi),
           SORT_FMT,
           BTOR_TRAPI_SORT_ID ((BtorSort *) codomain));
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);

  for (i = 0; i < arity; i++)
    BTOR_ABORT_BOOLECTOR (
        !BTOR_IS_BITVEC_SORT (BTOR_IMPORT_BOOLECTOR_SORT (domain[i]))
            && !BTOR_IS_BOOL_SORT (BTOR_IMPORT_BOOLECTOR_SORT (domain[i])),
        "'domain' sort at position %d must be a bool or bit vector sort",
        i);
  BTOR_ABORT_BOOLECTOR (
      !BTOR_IS_BITVEC_SORT (BTOR_IMPORT_BOOLECTOR_SORT (codomain))
          && !BTOR_IS_BOOL_SORT (BTOR_IMPORT_BOOLECTOR_SORT (codomain)),
      "'codomain' sort must be a bool or bit vector sort");

  res = btor_fun_sort (&btor->sorts_unique_table,
                       (BtorSort **) domain,
                       arity,
                       (BtorSort *) codomain);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BoolectorSort *cdomain[arity];
  for (i = 0; i < arity; i++)
    cdomain[i] = BTOR_CLONED_SORT (BTOR_IMPORT_BOOLECTOR_SORT (domain[i]));
  BTOR_CHKCLONE_RES_SORT (
      res,
      fun_sort,
      cdomain,
      arity,
      BTOR_CLONED_SORT (BTOR_IMPORT_BOOLECTOR_SORT (codomain)));
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

void
boolector_release_sort (Btor *btor, BoolectorSort *sort)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (sort);
  BTOR_TRAPI (SORT_FMT, BTOR_TRAPI_SORT_ID ((BtorSort *) sort));

  BtorSort *s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
#ifndef NDEBUG
  BoolectorSort *cs = BTOR_CLONED_SORT (s);
#endif
  assert (s->ext_refs > 0);
  dec_sort_ext_ref_counter (btor, s);
  btor_release_sort (&btor->sorts_unique_table, (BtorSort *) sort);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (release_sort, cs);
#endif
}

/*------------------------------------------------------------------------*/

/* Note: no need to trace parse function calls!! */

int
boolector_parse (Btor *btor,
                 FILE *file,
                 const char *file_name,
                 char **error_msg,
                 int *status)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file_name);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (error_msg);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (status);
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "file parsing must be done before creating expressions");
  res = btor_parse (btor, file, file_name, error_msg, status);
#ifndef NDEBUG
  if (btor->clone)
  {
    char *cerror_msg;
    int cstatus;
    FILE *cfile = fopen (file_name, "r");

    boolector_parse (btor->clone, cfile, file_name, &cerror_msg, &cstatus);
    assert (cstatus == *status);
    assert (!strcmp (cerror_msg, *error_msg));
    btor_chkclone (btor);
  }
#endif
  return res;
}

int
boolector_parse_btor (Btor *btor,
                      FILE *file,
                      const char *file_name,
                      char **error_msg,
                      int *status)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file_name);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (error_msg);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (status);
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "file parsing must be done before creating expressions");
  res = btor_parse_btor (btor, file, file_name, error_msg, status);
#ifndef NDEBUG
  if (btor->clone)
  {
    char *cerror_msg;
    int cstatus;
    FILE *cfile = fopen (file_name, "r");

    boolector_parse (btor->clone, cfile, file_name, &cerror_msg, &cstatus);
    assert (cstatus == *status);
    assert (!strcmp (cerror_msg, *error_msg));
    btor_chkclone (btor);
  }
#endif
  return res;
}

int
boolector_parse_smt1 (Btor *btor,
                      FILE *file,
                      const char *file_name,
                      char **error_msg,
                      int *status)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file_name);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (error_msg);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (status);
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "file parsing must be done before creating expressions");
  res = btor_parse_smt1 (btor, file, file_name, error_msg, status);
#ifndef NDEBUG
  if (btor->clone)
  {
    char *cerror_msg;
    int cstatus;
    FILE *cfile = fopen (file_name, "r");

    boolector_parse (btor->clone, cfile, file_name, &cerror_msg, &cstatus);
    assert (cstatus == *status);
    assert (!strcmp (cerror_msg, *error_msg));
    btor_chkclone (btor);
  }
#endif
  return res;
}

int
boolector_parse_smt2 (Btor *btor,
                      FILE *file,
                      const char *file_name,
                      char **error_msg,
                      int *status)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file_name);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (error_msg);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (status);
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "file parsing must be done before creating expressions");
  res = btor_parse_smt2 (btor, file, file_name, error_msg, status);
#ifndef NDEBUG
  if (btor->clone)
  {
    char *cerror_msg;
    int cstatus;
    FILE *cfile = fopen (file_name, "r");

    boolector_parse (btor->clone, cfile, file_name, &cerror_msg, &cstatus);
    assert (cstatus == *status);
    assert (!strcmp (cerror_msg, *error_msg));
    btor_chkclone (btor);
  }
#endif
  return res;
}

/*------------------------------------------------------------------------*/

void
boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor_dump_btor_node (btor, file, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor_node, file, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_dump_btor (Btor *btor, FILE *file)
{
  BTOR_TRAPI ("");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_BOOLECTOR (!btor_can_be_dumped (btor),
                        "formula cannot be dumped in BTOR format as it does "
                        "not support uninterpreted functions yet.");
  btor_dump_btor (btor, file, 1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor, file);
#endif
}

#if 0
void
boolector_dump_btor2 (Btor * btor, FILE * file)
{
  BTOR_TRAPI ("");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  btor_dump_btor (btor, file, 2);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor, file);
#endif
}
#endif

void
boolector_dump_smt1_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor_dump_smt1_nodes (btor, file, &exp, 1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt1_node, file, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_dump_smt1 (Btor *btor, FILE *file)
{
  BTOR_TRAPI ("");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  btor_dump_smt1 (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt1, file);
#endif
}

void
boolector_dump_smt2_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor_dump_smt2_nodes (btor, file, &exp, 1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt2_node, file, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_dump_smt2 (Btor *btor, FILE *file)
{
  BTOR_TRAPI ("");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  btor_dump_smt2 (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt2, file);
#endif
}

/* DEPRECATED API */

void
boolector_enable_model_gen (Btor *btor)
{
  BTOR_WARN_DEPRECATED ("boolector_set_opt");
  boolector_set_opt (btor, "model_gen", 1);
}

/* NOTE: for generating a model for all created expressions use --model-gen=2
 *	 instead */
void
boolector_generate_model_for_all_reads (Btor *btor)
{
  (void) btor;
}

void
boolector_enable_inc_usage (Btor *btor)
{
  BTOR_WARN_DEPRECATED ("boolector_set_opt");
  boolector_set_opt (btor, "incremental", 1);
}

void
boolector_set_rewrite_level (Btor *btor, int val)
{
  BTOR_WARN_DEPRECATED ("boolector_set_opt");
  boolector_set_opt (btor, "rewrite_level", val);
}

void
boolector_set_verbosity (Btor *btor, int val)
{
  BTOR_WARN_DEPRECATED ("boolector_set_opt");
  boolector_set_opt (btor, "verbosity", val);
}

void
boolector_set_loglevel (Btor *btor, int val)
{
  BTOR_WARN_DEPRECATED ("boolector_set_opt");
  boolector_set_opt (btor, "loglevel", val);
}

const char *
boolector_get_symbol_of_var (Btor *btor, BoolectorNode *node)
{
  BTOR_WARN_DEPRECATED ("boolector_get_symbol");
  return boolector_get_symbol (btor, node);
}

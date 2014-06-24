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
#include "btorclone.h"
#include "btorconst.h"
#include "btorcore.h"
#include "btorexit.h"
#include "btorhash.h"
#include "btoriter.h"
#include "btorsort.h"
#include "btortrapi.h"
#include "btorutil.h"
#include "dumper/btordumpbtor.h"
#include "dumper/btordumpsmt.h"

/*------------------------------------------------------------------------*/

#include <limits.h>
#include <stdio.h>
#include <string.h>

/*------------------------------------------------------------------------*/

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
boolector_chkclone (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
#ifndef BTOR_USE_LINGELING
  BTOR_ABORT_BOOLECTOR (1, "cloning requires lingeling as SAT solver");
#endif
  BTOR_TRAPI ("chkclone");
#ifndef NDEBUG
  if (btor->clone) btor_delete_btor (btor->clone);
  btor->clone = btor; /* mark clone as going-to-be shadow clone */
  btor->clone = btor_clone_btor (btor);
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
#endif

/*------------------------------------------------------------------------*/

Btor *
boolector_new (void)
{
  char *trname;
  Btor *btor;

  btor = btor_new_btor ();
  if ((trname = getenv ("BTORAPITRACE"))) btor_open_apitrace (btor, trname);
  BTOR_TRAPI ("new");
  return btor;
}

Btor *
boolector_clone (Btor *btor)
{
  BTOR_TRAPI ("clone"); /* just log, do nothing else */
  return btor_clone_btor (btor);
}

Btor *
boolector_btor (BoolectorNode *node)
{
  BtorNode *exp, *real_exp, *simp, *real_simp;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  real_exp  = BTOR_REAL_ADDR_NODE (exp);
  simp      = btor_simplify_exp (real_exp->btor, exp);
  real_simp = BTOR_REAL_ADDR_NODE (simp);
  btor      = real_simp->btor;
  assert (real_simp->btor == real_exp->btor);
  BTOR_TRAPI ("btor", exp);
#ifndef NDEBUG
  if (btor->clone)
  {
    Btor *clone = boolector_btor (BTOR_CLONED_EXP (exp));
    assert (clone == btor->clone);
    btor_chkclone (btor);
  }
#endif
  BTOR_TRAPI_RETURN_PTR (btor);
  return btor;
}

void
boolector_disable_pretty_print (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("disable_pretty_print");
  btor_disable_pretty_print (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (disable_pretty_print);
#endif
}

void
boolector_set_rewrite_level (Btor *btor, int rewrite_level)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("set_rewrite_level %d", rewrite_level);
  BTOR_ABORT_BOOLECTOR (rewrite_level < 0 || rewrite_level > 3,
                        "'rewrite_level' has to be in [0,3]");
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "setting rewrite level must be done before creating expressions");
  btor_set_rewrite_level_btor (btor, rewrite_level);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_rewrite_level, rewrite_level);
#endif
}

void
boolector_enable_model_gen (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_model_gen");
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "enabling model generation must be done before creating expressions");
  btor_enable_model_gen (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_model_gen);
#endif
}

void
boolector_disable_model_gen (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("disable_model_gen");
  btor_disable_model_gen (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (disable_model_gen);
#endif
}

void
boolector_generate_model_for_all_reads (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("generate_model_for_all_reads");
  btor_generate_model_for_all_reads (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (generate_model_for_all_reads);
#endif
}

void
boolector_enable_inc_usage (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_inc_usage");
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "enabling incremental usage must be done before calling 'boolector_sat'");
  btor_enable_inc_usage (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_inc_usage);
#endif
}

void
boolector_enable_beta_reduce_all (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_beta_reduce_all");
  btor_enable_beta_reduce_all (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_beta_reduce_all);
#endif
}

void
boolector_enable_dual_prop (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_dual_prop");
  BTOR_ABORT_BOOLECTOR (
      btor->options.just,
      "enabling multiple optimization techniques is not allowed");
  btor_enable_dual_prop (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_dual_prop);
#endif
}

void
boolector_enable_justification (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_just");
  BTOR_ABORT_BOOLECTOR (
      btor->options.dual_prop,
      "enabling multiple optimization techniques is not allowed");
  btor_enable_just (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_justification);
#endif
}
void
boolector_enable_force_cleanup (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_force_cleanup");
  btor_enable_force_cleanup (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_force_cleanup);
#endif
}

#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
void
boolector_enable_ucopt (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_ucopt");
  btor_enable_ucopt (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_ucopt);
#endif
}
#else
void
boolector_enable_ucopt (Btor *btor)
{
  (void) btor;
}
#endif

void
boolector_set_verbosity (Btor *btor, int verbosity)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("set_verbosity %d", verbosity);
  btor_set_verbosity_btor (btor, verbosity);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_verbosity, verbosity);
#endif
}

void
boolector_set_loglevel (Btor *btor, int loglevel)
{
#ifndef NBTORLOG
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("set_loglevel %d", loglevel);
  btor_set_loglevel_btor (btor, loglevel);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_loglevel, loglevel);
#endif
#else
  (void) btor;
  (void) loglevel;
#endif
}

int
boolector_set_sat_solver (Btor *btor, const char *solver)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("set_sat_solver %d", solver);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (solver);
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  res = btor_set_sat_solver (btor, solver);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, set_sat_solver, solver);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

void
boolector_reset_time (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("reset_time");
  btor_reset_time_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_time);
#endif
}

void
boolector_reset_stats (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("reset_stats");
  btor_reset_stats_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_stats);
#endif
}

int
boolector_get_refs (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("get_refs");
  res = btor->external_refs;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_refs);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

void
boolector_delete (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("delete");
  if (btor->closeapitrace == 1)
    fclose (btor->apitrace);
  else if (btor->closeapitrace == 2)
    pclose (btor->apitrace);
  if (btor->clone) boolector_delete (btor->clone);
  btor_delete_btor (btor);
}

int
boolector_simplify (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("simplify");

  res = btor_simplify (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, simplify);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

BoolectorNode *
boolector_const (Btor *btor, const char *bits)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("const %s", bits);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (bits);
  BTOR_ABORT_BOOLECTOR (*bits == '\0', "'bits' must not be empty");
  btor->external_refs++;
  res = btor_const_exp (btor, bits);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, const, bits);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
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
  BTOR_TRAPI ("is_const", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  simp = btor_simplify_exp (btor, exp);
  real = BTOR_REAL_ADDR_NODE (simp);
  res  = BTOR_IS_BV_CONST_NODE (real);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_const, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

const char *
boolector_get_bits (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *real;
  const char *res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
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

BoolectorNode *
boolector_zero (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("zero %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_zero_exp (btor, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, zero, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_false (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("false");
  btor->external_refs++;
  res = btor_false_exp (btor);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, false);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ones (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ones %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_ones_exp (btor, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ones, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_true (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("true");
  btor->external_refs++;
  res = btor_true_exp (btor);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, true);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_one (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("one %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_one_exp (btor, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, one, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_unsigned_int (Btor *btor, unsigned int u, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("unsigned_int %u %d", u, width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_unsigned_exp (btor, u, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, unsigned_int, u, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_int (Btor *btor, int i, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("int %d %u", i, width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_int_exp (btor, i, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, int, i, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_var (Btor *btor, int width, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  BtorNode *res;
  char *symb;

  if ((symb = (char *) symbol) == NULL)
  {
    BTOR_NEWN (btor->mm, symb, 20);
    sprintf (symb, "DVN%d", btor->dvn_id++);
    BTOR_TRAPI ("var %d %s", width, symb);
    BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
    btor->external_refs++;
    res = btor_var_exp (btor, width, symb);
  }
  else
  {
    BTOR_TRAPI ("var %d %s", width, symbol);
    BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
    btor->external_refs++;
    res = btor_var_exp (btor, width, symbol);
  }

  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;

  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, var, width, symbol);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

int
boolector_is_var (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *real;
  int res;
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI ("is_var", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  real = BTOR_REAL_ADDR_NODE (simp);
  res  = BTOR_IS_BV_VAR_NODE (real);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_const, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

BoolectorNode *
boolector_array (Btor *btor,
                 int elem_width,
                 int index_width,
                 const char *symbol)
{
  BtorNode *res;
  char *symb;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  if ((symb = (char *) symbol) == NULL)
  {
    BTOR_NEWN (btor->mm, symb, 20);
    sprintf (symb, "DAN%d", btor->dan_id++);
    BTOR_TRAPI ("array %d %d %s", elem_width, index_width, symb);
    BTOR_ABORT_BOOLECTOR (elem_width < 1, "'elem_width' must not be < 1");
    BTOR_ABORT_BOOLECTOR (index_width < 1, "'index_width' must not be < 1");
    btor->external_refs++;
    res = btor_array_exp (btor, elem_width, index_width, symb);
  }
  else
  {
    BTOR_TRAPI ("array %d %d %s", elem_width, index_width, symbol);
    BTOR_ABORT_BOOLECTOR (elem_width < 1, "'elem_width' must not be < 1");
    BTOR_ABORT_BOOLECTOR (index_width < 1, "'index_width' must not be < 1");
    btor->external_refs++;
    res = btor_array_exp (btor, elem_width, index_width, symbol);
  }
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, array, elem_width, index_width, symbol);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_not (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("not", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_not_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, not, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_neg (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("neg", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_neg_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, neg, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redor (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("redor", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_redor_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redor, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redxor (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("redxor", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_redxor_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redxor, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redand (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("redand", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_redand_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redand, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slice (Btor *btor, BoolectorNode *node, int upper, int lower)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT ("slice", exp, "%d %d", upper, lower);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (lower < 0, "'lower' must not be negative");
  BTOR_ABORT_BOOLECTOR (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT_BOOLECTOR (upper >= BTOR_REAL_ADDR_NODE (simp)->len,
                        "'upper' must not be >= width of 'exp'");
  btor->external_refs++;
  res = btor_slice_exp (btor, simp, upper, lower);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slice, BTOR_CLONED_EXP (exp), upper, lower);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uext (Btor *btor, BoolectorNode *node, int width)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT ("uext", exp, "%d", width);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  res = btor_uext_exp (btor, simp, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, uext, BTOR_CLONED_EXP (exp), width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sext (Btor *btor, BoolectorNode *node, int width)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT ("sext", exp, "%d", width);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  res = btor_sext_exp (btor, simp, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sext, BTOR_CLONED_EXP (exp), width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("implies", e0, e1);
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
  btor->external_refs++;
  res = btor_implies_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, implies, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("iff", e0, e1);
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
  btor->external_refs++;
  res = btor_iff_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, iff, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("xor", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_xor_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, xor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("xnor", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_xnor_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, xnor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("and", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_and_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, and, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("nand", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_nand_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nand, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("or", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_or_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, or, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("nor", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_nor_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_eq (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *real_simp0, *real_simp1, *res;
  int is_array_simp0, is_array_simp1;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("eq", e0, e1);
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
  BTOR_ABORT_BOOLECTOR (
      BTOR_IS_UF_NODE (real_simp0) || BTOR_IS_UF_NODE (real_simp1),
      "equality of UF not supported yet");
  BTOR_ABORT_BOOLECTOR (is_array_simp0 != is_array_simp1,
                        "array must not be compared to bit-vector");
  BTOR_ABORT_BOOLECTOR (!is_array_simp0 && real_simp0 && real_simp1
                            && real_simp0->len != real_simp1->len,
                        "bit-vectors must not have unequal bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp0 && real_simp0 && real_simp1
                            && real_simp0->len != real_simp1->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp0 && real_simp0 && real_simp1
                            && BTOR_ARRAY_INDEX_LEN (real_simp0)
                                   != BTOR_ARRAY_INDEX_LEN (real_simp1),
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  res = btor_eq_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, eq, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("ne", e0, e1);
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
  btor->external_refs++;
  res = btor_ne_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ne, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("add", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_add_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, add, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("uaddo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_uaddo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, uaddo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("saddo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_saddo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, saddo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("mul", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_mul_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, mul, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("umulo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_umulo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, umulo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("smulo", e0, e1);
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
  btor->external_refs++;
  res = btor_smulo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, smulo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("ult", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ult_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ult, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("slt", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_slt_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("ulte", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ulte_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ulte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("slte", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_slte_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("ugt", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ugt_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ugt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("sgt", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sgt_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sgt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("ugte", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ugte_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ugte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("sgte", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sgte_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sgte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("sll", e0, e1);
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
  btor->external_refs++;
  res = btor_sll_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sll, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("srl", e0, e1);
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
  btor->external_refs++;
  res = btor_srl_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, srl, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("sra", e0, e1);
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
  btor->external_refs++;
  res = btor_sra_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sra, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("rol", e0, e1);
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
  btor->external_refs++;
  res = btor_rol_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, rol, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("ror", e0, e1);
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
  btor->external_refs++;
  res = btor_ror_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ror, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("sub", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sub_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sub, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("usubo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_usubo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, usubo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("ssubo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ssubo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, ssubo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("udiv", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_udiv_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, udiv, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("sdiv", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sdiv_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sdiv, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("sdivo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sdivo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, sdivo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("urem", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_urem_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, urem, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("srem", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_srem_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, srem, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("smod", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_smod_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, smod, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("concat", e0, e1);
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
  btor->external_refs++;
  res = btor_concat_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, concat, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_BINFUN ("read", e_array, e_index);
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
  btor->external_refs++;
  res = btor_read_exp (btor, simp_array, simp_index);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, read, BTOR_CLONED_EXP (e_array), BTOR_CLONED_EXP (e_index));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_TERFUN ("write", e_array, e_index, e_value);
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
  btor->external_refs++;
  res = btor_write_exp (btor, simp_array, simp_index, simp_value);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res,
                         write,
                         BTOR_CLONED_EXP (e_array),
                         BTOR_CLONED_EXP (e_index),
                         BTOR_CLONED_EXP (e_value));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
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
  BTOR_TRAPI_TERFUN ("cond", e_cond, e_if, e_else);
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
  btor->external_refs++;
  res = btor_cond_exp (btor, simp_cond, simp_if, simp_else);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res,
                         cond,
                         BTOR_CLONED_EXP (e_cond),
                         BTOR_CLONED_EXP (e_if),
                         BTOR_CLONED_EXP (e_else));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_param (Btor *btor, int width, const char *symbol)
{
  BtorNode *res;
  char *symb;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  if ((symb = (char *) symbol) == NULL)
  {
    BTOR_NEWN (btor->mm, symb, 20);
    sprintf (symb, "DPN%d", btor->dpn_id++);
    BTOR_TRAPI ("param %d %s", width, symb);
    BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
    btor->external_refs++;
    res = btor_param_exp (btor, width, symb);
  }
  else
  {
    BTOR_TRAPI ("param %d %s", width, symbol);
    BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
    btor->external_refs++;
    res = btor_param_exp (btor, width, symbol);
  }
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;

  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, param, width, symbol);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_fun (Btor *btor,
               int paramc,
               BoolectorNode **param_nodes,
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
  sprintf (strtrapi, "fun %d", paramc);

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
  btor->external_refs++;
  res = btor_fun_exp (btor, paramc, params, exp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BoolectorNode *cparam_nodes[paramc];
  for (i = 0; btor->clone && i < paramc; i++)
    cparam_nodes[i] = BTOR_CLONED_EXP (params[i]);
  BTOR_CHKCLONE_RES_PTR (res, fun, paramc, cparam_nodes, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uf (Btor *btor, BoolectorSort *sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (sort);
  BTOR_ABORT_BOOLECTOR (((BtorSort *) sort)->kind != BTOR_FUN_SORT,
                        "given UF sort is not BTOR_FUN_SORT");
  BtorNode *res;

  res = btor_uf_exp (btor, (BtorSort *) sort, symbol);
  res->ext_refs++;
  btor->external_refs++;
  return (BoolectorNode *) res;
}

BoolectorSort *
boolector_bitvec_sort (Btor *btor, int len)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (len <= 0, "'len' must be > 0");

  BtorSort *res;
  res = btor_bitvec_sort (&btor->sorts_unique_table, len);
  res->ext_refs++;
  return (BoolectorSort *) res;
}

BoolectorSort *
boolector_tuple_sort (Btor *btor, BoolectorSort **elements, int num_elements)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (elements);
  BTOR_ABORT_BOOLECTOR (num_elements <= 1, "'num_elements' must be > 1");

  BtorSort *res;
  res = btor_tuple_sort (
      &btor->sorts_unique_table, (BtorSort **) elements, num_elements);
  res->ext_refs++;
  return (BoolectorSort *) res;
}

BoolectorSort *
boolector_fun_sort (Btor *btor, BoolectorSort *domain, BoolectorSort *codomain)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (domain);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (codomain);

  BtorSort *res;

  res = btor_fun_sort (
      &btor->sorts_unique_table, (BtorSort *) domain, (BtorSort *) codomain);
  res->ext_refs++;
  return (BoolectorSort *) res;
}

void
boolector_release_sort (Btor *btor, BoolectorSort *sort)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (sort);

  BtorSort *s = (BtorSort *) sort;
  assert (s->ext_refs > 0);
  s->ext_refs--;
  btor_release_sort (&btor->sorts_unique_table, (BtorSort *) sort);
}

BoolectorNode *
boolector_args (Btor *btor, int argc, BoolectorNode **arg_nodes)
{
  int i, len;
  char *strtrapi;
  BtorNode **args, *res;

  args = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (args);
  BTOR_ABORT_BOOLECTOR (argc < 1, "'argc' must not be < 1");

  len = 6 + 10 + argc * 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "args %d", argc);

  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_ARG_NULL_BOOLECTOR (args[i]);
    BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (args[i]);
    BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, args[i]);
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
  }
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  btor->external_refs++;
  res = btor_args_exp (btor, argc, args);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES_PTR (res, args, argc, carg_nodes);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_apply (Btor *btor,
                 int argc,
                 BoolectorNode **arg_nodes,
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
  sprintf (strtrapi, "apply %d", argc);

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
  btor->external_refs++;
  res = btor_apply_exps (btor, argc, args, e_fun);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES_PTR (res, apply, argc, carg_nodes, BTOR_CLONED_EXP (e_fun));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_apply_args (Btor *btor, BoolectorNode *n_args, BoolectorNode *n_fun)
{
  BtorNode *e_args, *e_fun, *res;

  e_args = BTOR_IMPORT_BOOLECTOR_NODE (n_args);
  e_fun  = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_args);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_fun);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_args);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_fun);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_args);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_fun);
  BTOR_TRAPI_BINFUN ("apply_args", e_args, e_fun);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_REGULAR_NODE (e_args),
                        "'args' must not be inverted");
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_ARGS_NODE (e_args),
                        "'args' is not an argument node");
  btor->external_refs++;
  res = btor_apply_exp (btor, e_fun, e_args);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, apply_args, BTOR_CLONED_EXP (e_args), BTOR_CLONED_EXP (e_fun));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_inc (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("inc", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);

  btor->external_refs++;
  res = btor_inc_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, inc, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_dec (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("dec", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);

  btor->external_refs++;
  res = btor_dec_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, dec, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

int
boolector_get_width (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("get_width", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  res = btor_get_exp_len (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_width, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
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
  BTOR_TRAPI_UNFUN ("is_array", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_array_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_array, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
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
  BTOR_TRAPI_UNFUN ("is_array_var", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_array_var_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_array_var, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
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
  BTOR_TRAPI_UNFUN ("is_param", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_param_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_param, node);
#endif
  BTOR_TRAPI_RETURN (res);
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
  BTOR_TRAPI_UNFUN ("is_param", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (simp)),
                        "given expression is not a parameter node");
  res = btor_is_bound_param_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_bound_param, node);
#endif
  BTOR_TRAPI_RETURN (res);
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
  BTOR_TRAPI_UNFUN ("is_fun", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_fun_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_fun, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
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
  BTOR_TRAPI_UNFUN ("get_fun_arity", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (!btor_is_fun_exp (btor, simp),
                        "given expression is not a function node");
  res = btor_get_fun_arity (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_fun_arity, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_is_args (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("is_args", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_args_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_args, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_get_args_arity (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("get_args_arity", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (simp)),
                        "given expression is not an argument node");
  res = btor_get_args_arity (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_args_arity, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
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
  BTOR_TRAPI_UNFUN ("get_index_width", e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  simp_array = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (simp_array);
  res = btor_get_index_exp_len (btor, simp_array);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_index_width, BTOR_CLONED_EXP (e_array));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_fun_sort_check (Btor *btor,
                          int argc,
                          BoolectorNode **arg_nodes,
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
  sprintf (strtrapi, "fun_sort_check %d", argc);

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
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES (
      res, fun_sort_check, argc, carg_nodes, BTOR_CLONED_EXP (e_fun));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

const char *
boolector_get_symbol_of_var (Btor *btor, BoolectorNode *node)
{
  const char *res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("get_symbol_of_var", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  res = (const char *) btor_get_symbol_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_STR (res, get_symbol_of_var, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_STR (res);
  return res;
}

BoolectorNode *
boolector_copy (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("copy", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor->external_refs++;
  res = btor_copy_exp (btor, exp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, copy, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

void
boolector_release (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("release", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor->external_refs--;
#ifndef NDEBUG
  BoolectorNode *cexp = BTOR_CLONED_EXP (exp);
#endif
  assert (BTOR_REAL_ADDR_NODE (exp)->ext_refs);
  BTOR_REAL_ADDR_NODE (exp)->ext_refs -= 1;
  btor_release_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (release, cexp);
#endif
}

void
boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  // TODO TRAPI
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
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
  BTOR_TRAPI ("dump_btor");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  btor_dump_btor (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor, file);
#endif
}

void
boolector_dump_smt1_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  // TODO TRAPI
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
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
  BTOR_TRAPI ("dump_smt1");
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
  // TODO TRAPI
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
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
  BTOR_TRAPI ("dump_smt2");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  btor_dump_smt2 (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt2, file);
#endif
}

void
boolector_assert (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI_UNFUN ("assert", exp);
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
  BTOR_TRAPI_UNFUN ("assume", exp);
  BTOR_ABORT_BOOLECTOR (!btor->options.inc_enabled,
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
  BTOR_TRAPI_UNFUN ("failed", exp);
  BTOR_ABORT_BOOLECTOR (!btor->options.inc_enabled,
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
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, failed, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_sat (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sat");
  BTOR_ABORT_BOOLECTOR (
      !btor->options.inc_enabled && btor->btor_sat_btor_called > 0,
      "incremental usage has not been enabled."
      "'boolector_sat' may only be called once");
  res = btor_sat_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, sat);
#endif
  BTOR_TRAPI_RETURN (res);
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
  BTOR_TRAPI_UNFUN ("bv_assignment", exp);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_SAT,
      "cannot retrieve assignment if input formula is not SAT");
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (!btor->options.model_gen,
                        "model generation has not been enabled");
  ass   = btor_bv_assignment_str (btor, simp);
  bvass = btor_new_bv_assignment (btor->bv_assignments, (char *) ass);
  btor_release_bv_assignment_str (btor, (char *) ass);
  res = btor_get_bv_assignment_str (bvass);
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
  BTOR_TRAPI_RETURN_PTR (res);
  return res;
}

void
boolector_free_bv_assignment (Btor *btor, const char *assignment)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("free_bv_assignment %p", assignment);
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
  BTOR_TRAPI_UNFUN ("array_assignment", e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (indices);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (values);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (size);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  simp = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (!btor->options.model_gen,
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
  /* special case: we treat out parameters as return values for btoruntrace */
  BTOR_TRAPI ("return %p %p %d", *indices, *values, *size);
}

void
boolector_free_array_assignment (Btor *btor,
                                 char **indices,
                                 char **values,
                                 int size)
{
  BtorArrayAssignment *arrass;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("free_array_assignment %p %p %d", indices, values, size);
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

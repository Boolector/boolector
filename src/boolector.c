/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2016 Armin Biere.
 *  Copyright (C) 2012-2018 Mathias Preiner.
 *  Copyright (C) 2013-2019 Aina Niemetz.
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
#include "btorexp.h"
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
abort_aux (const char* msg)
{
  if (btor_abort_callback.cb_fun)
    ((void (*) (const char*)) btor_abort_callback.cb_fun) (msg);
}

BtorAbortCallback btor_abort_callback = {
    .abort_fun = abort_aux, .cb_fun = btor_abort_fun};

/*------------------------------------------------------------------------*/

static void
inc_sort_ext_ref_counter (Btor *btor, BtorSortId id)
{
  assert (btor);
  assert (id);

  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);

  BTOR_ABORT (sort->ext_refs == INT32_MAX, "Node reference counter overflow");
  sort->ext_refs += 1;
  btor->external_refs += 1;
}

static void
dec_sort_ext_ref_counter (Btor *btor, BtorSortId id)
{
  assert (btor);
  assert (id);

  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort->ext_refs > 0);
  sort->ext_refs -= 1;
  btor->external_refs -= 1;
}

/*------------------------------------------------------------------------*/

static BtorNode *
translate_shift (Btor *btor,
                 BtorNode *a0,
                 BtorNode *a1,
                 BtorNode *(*f) (Btor *, BtorNode *, BtorNode *) )
{
  BtorNode *c, *e, *t, *e0, *u, *l, *tmp, *res;
  BtorSortId s;
  uint32_t width, l0, l1, p0, p1;

  width = btor_node_bv_get_width (btor, a0);

  assert (width == btor_node_bv_get_width (btor, a1));

  l1 = 0;
  for (l0 = 1; l0 < width; l0 *= 2) l1++;

  assert (l0 == (1u << l1));

  if (width == 1)
  {
    assert (l0 == 1);
    assert (l1 == 0);

    if (f != btor_exp_bv_sra)
    {
      tmp = btor_exp_bv_not (btor, a1);
      res = btor_exp_bv_and (btor, a0, tmp);
      btor_node_release (btor, tmp);
    }
    else
      res = btor_node_copy (btor, a0);
  }
  else
  {
    assert (width >= 1);
    assert (width <= l0);

    p0 = l0 - width;
    p1 = width - l1;

    assert (p1 > 0);

    u = btor_exp_bv_slice (btor, a1, width - 1, width - p1);
    l = btor_exp_bv_slice (btor, a1, l1 - 1, 0);

    assert (btor_node_bv_get_width (btor, u) == p1);
    assert (btor_node_bv_get_width (btor, l) == l1);

    if (p1 > 1)
      c = btor_exp_bv_redor (btor, u);
    else
      c = btor_node_copy (btor, u);

    btor_node_release (btor, u);

    if (f == btor_exp_bv_sra)
    {
      tmp = btor_exp_bv_slice (btor, a0, width - 1, width - 1);
      t   = btor_exp_bv_sext (btor, tmp, width - 1);
      btor_node_release (btor, tmp);
    }
    else
    {
      s = btor_sort_bv (btor, width);
      t = btor_exp_bv_zero (btor, s);
      btor_sort_release (btor, s);
    }

    if (!p0)
      e0 = btor_node_copy (btor, a0);
    else if (f == btor_exp_bv_sra)
      e0 = btor_exp_bv_sext (btor, a0, p0);
    else
      e0 = btor_exp_bv_uext (btor, a0, p0);

    assert (btor_node_bv_get_width (btor, e0) == l0);

    e = f (btor, e0, l);
    btor_node_release (btor, e0);
    btor_node_release (btor, l);

    if (p0 > 0)
    {
      tmp = btor_exp_bv_slice (btor, e, width - 1, 0);
      btor_node_release (btor, e);
      e = tmp;
    }

    res = btor_exp_cond (btor, c, t, e);

    btor_node_release (btor, c);
    btor_node_release (btor, t);
    btor_node_release (btor, e);
  }
  return res;
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
  uint32_t i;

  if (btor->clone)
  {
    /* force auto cleanup (might have been disabled via btormbt) */
    btor_opt_set (btor->clone, BTOR_OPT_AUTO_CLEANUP, 1);
    btor_delete (btor->clone);
    btor->clone = 0;
  }
  /* do not generate shadow clone if sat solver does not support cloning
   * (else only expression layer will be cloned and shadowed API function
   *  calls may fail) */
  if (!btor_sat_mgr_has_clone_support (btor_get_sat_mgr (btor))) return;
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
                      btor_node_is_inverted (exp)                            \
                          ? btor_node_invert (BTOR_PEEK_STACK (              \
                                btor->clone->nodes_id_table,                 \
                                btor_node_real_addr (exp)->id))              \
                          : BTOR_PEEK_STACK (btor->clone->nodes_id_table,    \
                                             btor_node_real_addr (exp)->id)) \
                : 0))

#else
#define BTOR_CLONED_EXP(exp) 0
#endif

/*------------------------------------------------------------------------*/

/* for internal use (parser), only */

void
boolector_set_btor_id (Btor *btor, BoolectorNode *node, int32_t id)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI_UNFUN_EXT (exp, "%d", id);
  BTOR_ABORT (!btor_node_is_bv_var (exp) && !btor_node_is_uf_array (exp),
              "'exp' is neither BV/array variable nor UF");
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  btor_node_set_btor_id (btor, exp, id);
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
  BTOR_ABORT (btor->quantifiers->count,
              "models are currently not supported with quantifiers");
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  btor_print_value_smt2 (btor, exp, symbol_str, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (
      print_value_smt2, BTOR_CLONED_EXP (exp), symbol_str, file);
#endif
}

void
boolector_add_output (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_ARG_NULL (node);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_PUSH_STACK (btor->outputs, btor_node_copy (btor, exp));
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (add_output, BTOR_CLONED_EXP (exp));
#endif
}

/*------------------------------------------------------------------------*/

Btor *
boolector_new (void)
{
  char *trname;
  Btor *btor;

  btor = btor_new ();
  if ((trname = getenv ("BTORAPITRACE"))) btor_trapi_open_trace (btor, trname);
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
    btor_delete (cshadow);
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
  btor_delete (btor);
}

void
boolector_set_term (Btor *btor, int32_t (*fun) (void *), void *state)
{
  BTOR_ABORT_ARG_NULL (btor);
  btor_set_term (btor, fun, state);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_term, fun, state);
#endif
}

int32_t
boolector_terminate (Btor *btor)
{
  int32_t res;

  BTOR_ABORT_ARG_NULL (btor);
  res = btor_terminate (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_INT (res, terminate);
#endif
  return res;
}

void
boolector_set_abort (void (*fun) (const char* msg))
{
  btor_abort_callback.abort_fun = abort_aux;
  btor_abort_callback.cb_fun = fun;
}

void
boolector_set_msg_prefix (Btor *btor, const char *prefix)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%s", prefix);
  btor_set_msg_prefix (btor, prefix);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_msg_prefix, prefix);
#endif
}

uint32_t
boolector_get_refs (Btor *btor)
{
  uint32_t res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  res = btor->external_refs;
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_refs);
#endif
  return res;
}

void
boolector_reset_time (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  btor_reset_time (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_time);
#endif
}

void
boolector_reset_stats (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  btor_reset_stats (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_stats);
#endif
}

void
boolector_print_stats (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  btor_sat_print_stats (btor_get_sat_mgr (btor));
  btor_print_stats (btor);
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
boolector_push (Btor *btor, uint32_t level)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%u", level);
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL),
              "incremental usage has not been enabled");
  BTOR_ABORT (level < 1, "context level must be greater than 0");

  uint32_t i;
  for (i = 0; i < level; i++)
  {
    BTOR_PUSH_STACK (btor->assertions_trail,
                     BTOR_COUNT_STACK (btor->assertions));
  }
  btor->num_push_pop++;
}

void
boolector_pop (Btor *btor, uint32_t level)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%u", level);
  BTOR_ABORT (level < 1, "context level must be greater than 0");
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL),
              "incremental usage has not been enabled");
  BTOR_ABORT (level > BTOR_COUNT_STACK (btor->assertions_trail),
              "can not pop more levels (%u) than created via push (%u).",
              level,
              BTOR_COUNT_STACK (btor->assertions_trail));

  uint32_t i, pos = 0;
  for (i = 0; i < level; i++) pos = BTOR_POP_STACK (btor->assertions_trail);

  BtorNode *cur;
  while (BTOR_COUNT_STACK (btor->assertions) > pos)
  {
    cur = BTOR_POP_STACK (btor->assertions);
    btor_hashint_table_remove (btor->assertions_cache, btor_node_get_id (cur));
    btor_node_release (btor, cur);
  }
  btor->num_push_pop++;
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
  BTOR_ABORT (btor_node_bv_get_width (btor, exp) != 1,
              "'exp' must have bit-width one");
  BTOR_ABORT (!btor_sort_is_bool (btor, btor_node_real_addr (exp)->sort_id),
              "'exp' must have bit-width one");
  BTOR_ABORT (btor_node_real_addr (exp)->parameterized,
              "assertion must not be parameterized");

  /* all assertions at a context level > 0 are internally handled as
   * assumptions. */
  if (BTOR_COUNT_STACK (btor->assertions_trail) > 0)
  {
    int32_t id = btor_node_get_id (exp);
    if (!btor_hashint_table_contains (btor->assertions_cache, id))
    {
      BTOR_PUSH_STACK (btor->assertions, btor_node_copy (btor, exp));
      btor_hashint_table_add (btor->assertions_cache, id);
    }
  }
  else
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
  BTOR_ABORT (!btor_sort_is_bool (btor, btor_node_real_addr (exp)->sort_id),
              "'exp' must have bit-width one");
  BTOR_ABORT (btor_node_real_addr (exp)->parameterized,
              "assumption must not be parameterized");
  BTOR_PUSH_STACK (btor->failed_assumptions, btor_node_copy (btor, exp));
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
  BTOR_ABORT (btor_node_bv_get_width (btor, exp) != 1,
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

BoolectorNode **
boolector_get_failed_assumptions (Btor *btor)
{
  BoolectorNode **res;
  BtorNodePtrStack failed;
  BtorNode *fass;
  uint32_t i;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (btor->last_sat_result != BTOR_RESULT_UNSAT,
              "cannot check failed assumptions if input formula is not UNSAT");

  BTOR_INIT_STACK (btor->mm, failed);
  for (i = 0; i < BTOR_COUNT_STACK (btor->failed_assumptions); i++)
  {
    fass = BTOR_PEEK_STACK (btor->failed_assumptions, i);
    if (!fass) continue;
    assert (btor_hashptr_table_get (
        btor->assumptions, btor_pointer_chase_simplified_exp (btor, fass)));
    if (btor_failed_exp (btor, fass))
      BTOR_PUSH_STACK (failed, fass);
    else
      btor_node_release (btor, fass);
  }
  BTOR_PUSH_STACK (failed, NULL);
  BTOR_RELEASE_STACK (btor->failed_assumptions);
  btor->failed_assumptions = failed;
  res                      = (BoolectorNode **) btor->failed_assumptions.start;
#ifndef NDEBUG
  if (btor->clone)
  {
    BoolectorNode **cloneres;
    cloneres = boolector_get_failed_assumptions (btor->clone);
    for (i = 0; res[i] != NULL; i++)
      btor_chkclone_exp (btor,
                         btor->clone,
                         BTOR_IMPORT_BOOLECTOR_NODE (res[i]),
                         BTOR_IMPORT_BOOLECTOR_NODE (cloneres[i]));
    btor_chkclone (btor, btor->clone);
  }
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

/*------------------------------------------------------------------------*/

int32_t
boolector_sat (Btor *btor)
{
  int32_t res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
                  && btor->btor_sat_btor_called > 0,
              "incremental usage has not been enabled."
              "'boolector_sat' may only be called once");
  res = btor_check_sat (btor, -1, -1);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_INT (res, sat);
#endif
  return res;
}

int32_t
boolector_limited_sat (Btor *btor, int32_t lod_limit, int32_t sat_limit)
{
  int32_t res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d %d", lod_limit, sat_limit);
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
                  && btor->btor_sat_btor_called > 0,
              "incremental usage has not been enabled."
              "'boolector_limited_sat' may only be called once");
  res = btor_check_sat (btor, lod_limit, sat_limit);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_INT (res, limited_sat, lod_limit, sat_limit);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

int32_t
boolector_simplify (Btor *btor)
{
  int32_t res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");

  res = btor_simplify (btor);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_INT (res, simplify);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

void
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

  if (!strcasecmp (solver, "lingeling"))
    sat_engine = BTOR_SAT_ENGINE_LINGELING;
  else if (!strcasecmp (solver, "picosat"))
    sat_engine = BTOR_SAT_ENGINE_PICOSAT;
  else if (!strcasecmp (solver, "minisat"))
    sat_engine = BTOR_SAT_ENGINE_MINISAT;
  else if (!strcasecmp (solver, "cadical"))
    sat_engine = BTOR_SAT_ENGINE_CADICAL;
  else
    BTOR_ABORT (1, "invalid sat engine '%s' selected", solver);

#if !defined(BTOR_USE_LINGELING) || !defined(BTOR_USE_CADICAL) \
    || !defined(BTOR_USE_MINISAT) || !defined(BTOR_USE_PICOSAT)
  uint32_t oldval = btor_opt_get (btor, BTOR_OPT_SAT_ENGINE);
#endif
#ifndef BTOR_USE_LINGELING
  if (sat_engine == BTOR_SAT_ENGINE_LINGELING)
  {
    BTOR_WARN (
        true,
        "SAT solver Lingeling not compiled in, using %s",
        oldval == BTOR_SAT_ENGINE_CADICAL
            ? "CaDiCaL"
            : (oldval == BTOR_SAT_ENGINE_MINISAT ? "MiniSat" : "PicoSAT"));
    sat_engine = oldval;
  }
#endif
#ifndef BTOR_USE_CADICAL
  if (sat_engine == BTOR_SAT_ENGINE_CADICAL)
  {
    BTOR_WARN (
        true,
        "SAT solver CaDiCaL not compiled in, using %s",
        oldval == BTOR_SAT_ENGINE_LINGELING
            ? "Lingeling"
            : (oldval == BTOR_SAT_ENGINE_MINISAT ? "MiniSat" : "PicoSAT"));
    sat_engine = oldval;
  }
#endif
#ifndef BTOR_USE_MINISAT
  if (sat_engine == BTOR_SAT_ENGINE_MINISAT)
  {
    BTOR_WARN (
        sat_engine == BTOR_SAT_ENGINE_MINISAT,
        "SAT solver Minisat not compiled in, using %s",
        oldval == BTOR_SAT_ENGINE_CADICAL
            ? "CaDiCaL"
            : (oldval == BTOR_SAT_ENGINE_LINGELING ? "Lingeling" : "PicoSAT"));
    sat_engine = oldval;
  }
#endif
#ifndef BTOR_USE_PICOSAT
  if (sat_engine == BTOR_SAT_ENGINE_PICOSAT)
  {
    BTOR_WARN (
        sat_engine == BTOR_SAT_ENGINE_PICOSAT,
        "SAT solver PicoSAT not compiled in, using %s",
        oldval == BTOR_SAT_ENGINE_CADICAL
            ? "CaDiCaL"
            : (oldval == BTOR_SAT_ENGINE_LINGELING ? "Lingeling" : "MiniSat"));
    sat_engine = oldval;
  }
#endif

  btor_opt_set (btor, BTOR_OPT_SAT_ENGINE, sat_engine);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_sat_solver, solver);
#endif
}

/*------------------------------------------------------------------------*/

void
boolector_set_opt (Btor *btor, BtorOption opt, uint32_t val)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%s %u", btor_opt_get_lng (btor, opt), val);
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

#if !defined(BTOR_USE_LINGELING) || !defined(BTOR_USE_CADICAL) \
    || !defined(BTOR_USE_MINISAT) || !defined(BTOR_USE_PICOSAT)
  uint32_t oldval = btor_opt_get (btor, opt);
#endif

  if (opt == BTOR_OPT_SAT_ENGINE)
  {
#ifndef BTOR_USE_LINGELING
    if (val == BTOR_SAT_ENGINE_LINGELING)
    {
      BTOR_WARN (
          true,
          "SAT solver Lingeling not compiled in, using %s",
          oldval == BTOR_SAT_ENGINE_CADICAL
              ? "CaDiCaL"
              : (oldval == BTOR_SAT_ENGINE_MINISAT ? "MiniSat" : "PicoSAT"));
      val = oldval;
    }
#endif
#ifndef BTOR_USE_CADICAL
    if (val == BTOR_SAT_ENGINE_CADICAL)
    {
      BTOR_WARN (
          true,
          "SAT solver CaDiCaL not compiled in, using %s",
          oldval == BTOR_SAT_ENGINE_LINGELING
              ? "Lingeling"
              : (oldval == BTOR_SAT_ENGINE_MINISAT ? "MiniSat" : "PicoSAT"));
      val = oldval;
    }
#endif
#ifndef BTOR_USE_MINISAT
    if (val == BTOR_SAT_ENGINE_MINISAT)
    {
      BTOR_WARN (val == BTOR_SAT_ENGINE_MINISAT,
                 "SAT solver Minisat not compiled in, using %s",
                 oldval == BTOR_SAT_ENGINE_CADICAL
                     ? "CaDiCaL"
                     : (oldval == BTOR_SAT_ENGINE_LINGELING ? "Lingeling"
                                                            : "PicoSAT"));
      val = oldval;
    }
#endif
#ifndef BTOR_USE_PICOSAT
    if (val == BTOR_SAT_ENGINE_PICOSAT)
    {
      BTOR_WARN (val == BTOR_SAT_ENGINE_PICOSAT,
                 "SAT solver PicoSAT not compiled in, using %s",
                 oldval == BTOR_SAT_ENGINE_CADICAL
                     ? "CaDiCaL"
                     : (oldval == BTOR_SAT_ENGINE_LINGELING ? "Lingeling"
                                                            : "MiniSat"));
      val = oldval;
    }
#endif
  }

#ifndef BTOR_USE_LINGELING
  if (opt == BTOR_OPT_SAT_ENGINE_LGL_FORK)
  {
    val = oldval;
    BTOR_MSG (btor->msg,
              1,
              "SAT solver Lingeling not compiled in, will not set option "
              "to clone/fork Lingeling");
  }
#endif

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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  BTOR_TRAPI ("%s", btor_opt_get_lng (btor, opt));
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
  res = btor_node_copy (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
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
  assert (btor_node_real_addr (exp)->ext_refs);
  btor_node_dec_ext_ref_counter (btor, exp);
  btor_node_release (btor, exp);
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

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_true (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  res = btor_exp_true (btor);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, true);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_false (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("");
  res = btor_exp_false (btor);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, false);
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
  BTOR_ABORT (btor_node_bv_get_width (btor, e0) != 1
                  || btor_node_bv_get_width (btor, e1) != 1,
              "bit-width of 'e0' and 'e1' must be 1");
  res = btor_exp_implies (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT (btor_node_bv_get_width (btor, e0) != 1
                  || btor_node_bv_get_width (btor, e1) != 1,
              "bit-width of 'e0' and 'e1' must not be unequal to 1");
  res = btor_exp_iff (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, iff, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

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
  BTOR_ABORT (btor_node_get_sort_id (e0) != btor_node_get_sort_id (e1)
                  || btor_node_real_addr (e0)->is_array
                         != btor_node_real_addr (e1)->is_array,
              "nodes must have equal sorts");
  BTOR_ABORT (btor_sort_is_fun (btor, btor_node_get_sort_id (e0))
                  && (btor_node_real_addr (e0)->parameterized
                      || btor_node_real_addr (e1)->parameterized),
              "parameterized function equalities not supported");
  res = btor_exp_eq (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT (btor_node_get_sort_id (e0) != btor_node_get_sort_id (e1),
              "nodes must have equal sorts");
  BTOR_ABORT (btor_sort_is_fun (btor, btor_node_get_sort_id (e0))
                  && (btor_node_real_addr (e0)->parameterized
                      || btor_node_real_addr (e1)->parameterized),
              "parameterized function equalities not supported");
  res = btor_exp_ne (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ne, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

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
  res = btor_exp_bv_const (btor, bv);
  btor_node_inc_ext_ref_counter (btor, res);
  btor_bv_free (btor->mm, bv);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, const, bits);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_constd (Btor *btor, BoolectorSort sort, const char *str)
{
  uint32_t w;
  BtorNode *res;
  BtorBitVector *bv;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT " %s", sort, str);
  BTOR_ABORT_ARG_NULL (str);
  BTOR_ABORT (*str == '\0', "'str' must not be empty");

  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  w = btor_sort_bv_get_width (btor, s);
  BTOR_ABORT (!btor_util_check_dec_to_bv (btor->mm, str, w),
              "'%s' does not fit into a bit-vector of size %u",
              str,
              w);
  bv  = btor_bv_constd (btor->mm, str, w);
  res = btor_exp_bv_const (btor, bv);
  assert (btor_node_get_sort_id (res) == s);
  btor_bv_free (btor->mm, bv);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, constd, sort, str);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_consth (Btor *btor, BoolectorSort sort, const char *str)
{
  uint32_t w;
  BtorNode *res;
  BtorBitVector *bv;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%s", str);
  BTOR_ABORT_ARG_NULL (str);
  BTOR_ABORT (*str == '\0', "'str' must not be empty");

  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  w = btor_sort_bv_get_width (btor, s);
  BTOR_ABORT (!btor_util_check_hex_to_bv (btor->mm, str, w),
              "'%s' does not fit into a bit-vector of size %u",
              str,
              w);
  bv  = btor_bv_consth (btor->mm, str, w);
  res = btor_exp_bv_const (btor, bv);
  assert (btor_node_get_sort_id (res) == s);
  btor_bv_free (btor->mm, bv);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, consth, sort, str);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_zero (Btor *btor, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_exp_bv_zero (btor, s);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, zero, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ones (Btor *btor, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_exp_bv_ones (btor, s);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ones, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_one (Btor *btor, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_exp_bv_one (btor, s);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, one, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_min_signed (Btor *btor, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s), "'sort' is not a bit vector sort");
  res = btor_exp_bv_min_signed (btor, s);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, min_signed, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_max_signed (Btor *btor, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s), "'sort' is not a bit vector sort");
  res = btor_exp_bv_max_signed (btor, s);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, max_signed, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_unsigned_int (Btor *btor, uint32_t u, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%u " BTOR_TRAPI_SORT_FMT, u, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_exp_bv_unsigned (btor, u, s);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, unsigned_int, u, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_int (Btor *btor, int32_t i, BoolectorSort sort)
{
  BtorNode *res;
  BtorSortId s;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%d " BTOR_TRAPI_SORT_FMT, i, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  res = btor_exp_bv_int (btor, i, s);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, int, i, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

/* Remove unique symbol prefix and return start address of original symbol
 * without prefix. */
static const char *
remove_unique_symbol_prefix (Btor *btor, const char *symbol)
{
  if (symbol)
  {
    size_t len    = strlen (symbol);
    size_t offset = 5 + btor_util_num_digits (btor->num_push_pop);
    if (len > offset && !strncmp (symbol, "BTOR_", 5) && symbol[offset] == '@')
    {
      return symbol + offset + 1;
    }
  }
  return symbol;
}

/* Create symbol that is unique in the current scope. Prefix symbols with
 * BTOR_<num_push_pop>@<symbol> to make them unique in the current context. */
static char *
mk_unique_symbol (Btor *btor, const char *symbol)
{
  char *symb;
  size_t len;
  if (btor->num_push_pop)
  {
    len = strlen (symbol) + 1;
    len += strlen ("BTOR_@");
    len += btor_util_num_digits (btor->num_push_pop);
    BTOR_CNEWN (btor->mm, symb, len);
    sprintf (symb, "BTOR_%u@%s", btor->num_push_pop, symbol);
  }
  else
  {
    symb = btor_mem_strdup (btor->mm, symbol);
  }
  assert (!symbol
          || !strcmp (symbol, remove_unique_symbol_prefix (btor, symb)));
  return symb;
}

BoolectorNode *
boolector_var (Btor *btor, BoolectorSort sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL (btor);

  BtorNode *res;
  char *symb;
  BtorSortId s;

  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  symb = mk_unique_symbol (btor, symbol);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT " %s", sort, btor, symb);
  BTOR_ABORT (symb && btor_hashptr_table_get (btor->symbols, (char *) symb),
              "symbol '%s' is already in use in the current context",
              symb);
  res = btor_exp_var (btor, s, symb);
  btor_mem_freestr (btor->mm, symb);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
  (void) btor_hashptr_table_add (btor->inputs, btor_node_copy (btor, res));
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

  symb = mk_unique_symbol (btor, symbol);
  s    = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_fun (btor, s)
                  || btor_sort_tuple_get_arity (
                         btor, btor_sort_fun_get_domain (btor, s))
                         != 1,
              "'sort' is not an array sort");
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT " %s", sort, btor, symb);
  BTOR_ABORT (symb && btor_hashptr_table_get (btor->symbols, symb),
              "symbol '%s' is already in use in the current context",
              symb);
  res = btor_exp_array (btor, s, symb);
  btor_mem_freestr (btor->mm, symb);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
  (void) btor_hashptr_table_add (btor->inputs, btor_node_copy (btor, res));
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

  symb = mk_unique_symbol (btor, symbol);
  s    = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT "%s", sort, btor, symb);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_fun (btor, s),
              "%ssort%s%s%s%s must be a function sort",
              symbol ? "" : "'",
              symbol ? "" : "'",
              symbol ? " '" : "",
              symbol ? symbol : "",
              symbol ? "'" : "");
  BTOR_ABORT (symb && btor_hashptr_table_get (btor->symbols, symb),
              "symbol '%s' is already in use in the current context",
              symb);

  res = btor_exp_uf (btor, s, symb);
  btor_mem_freestr (btor->mm, symb);
  assert (btor_node_is_regular (res));
  btor_node_inc_ext_ref_counter (btor, res);
  (void) btor_hashptr_table_add (btor->inputs, btor_node_copy (btor, res));
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, uf, sort, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

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
  res = btor_exp_bv_not (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
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
  res = btor_exp_bv_neg (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
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
  res = btor_exp_bv_redor (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
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
  res = btor_exp_bv_redxor (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
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
  res = btor_exp_bv_redand (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_TRAPI_UNFUN_EXT (exp, "%u %u", upper, lower);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT ((uint32_t) upper >= btor_node_bv_get_width (btor, exp),
              "'upper' must not be >= width of 'exp'");
  res = btor_exp_bv_slice (btor, exp, upper, lower);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slice, BTOR_CLONED_EXP (exp), upper, lower);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uext (Btor *btor, BoolectorNode *node, uint32_t width)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%u", width);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (width > UINT32_MAX - btor_node_bv_get_width (btor, exp),
              "extending 'exp' (width %u) by %u bits exceeds maximum "
              "bit-width of %u",
              btor_node_bv_get_width (btor, exp),
              width,
              UINT32_MAX);
  res = btor_exp_bv_uext (btor, exp, width);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, uext, BTOR_CLONED_EXP (exp), width);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sext (Btor *btor, BoolectorNode *node, uint32_t width)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%u", width);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (width > UINT32_MAX - btor_node_bv_get_width (btor, exp),
              "extending 'exp' (width %u) by %u bits exceeds maximum "
              "bit-width of %u",
              btor_node_bv_get_width (btor, exp),
              width,
              UINT32_MAX);
  res = btor_exp_bv_sext (btor, exp, width);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sext, BTOR_CLONED_EXP (exp), width);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_xor (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_xnor (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_and (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_nand (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_or (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_nor (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_add (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_uaddo (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_saddo (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_mul (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_umulo (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_smulo (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_ult (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_slt (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_ulte (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_slte (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_ugt (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_sgt (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_ugte (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_sgte (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sgte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sll (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width;
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

  width = btor_node_bv_get_width (btor, e0);
  if (width == btor_node_bv_get_width (btor, e1))
  {
    res = translate_shift (btor, e0, e1, btor_exp_bv_sll);
  }
  else
  {
    BTOR_ABORT (!btor_util_is_power_of_2 (width),
                "bit-width of 'e0' must be a power of 2");
    BTOR_ABORT (btor_util_log_2 (width) != btor_node_bv_get_width (btor, e1),
                "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
    res = btor_exp_bv_sll (btor, e0, e1);
  }
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sll, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_srl (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width;
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
  width = btor_node_bv_get_width (btor, e0);
  if (width == btor_node_bv_get_width (btor, e1))
  {
    res = translate_shift (btor, e0, e1, btor_exp_bv_srl);
  }
  else
  {
    BTOR_ABORT (!btor_util_is_power_of_2 (width),
                "bit-width of 'e0' must be a power of 2");
    BTOR_ABORT (btor_util_log_2 (width) != btor_node_bv_get_width (btor, e1),
                "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
    res = btor_exp_bv_srl (btor, e0, e1);
  }
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, srl, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sra (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width;
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
  width = btor_node_bv_get_width (btor, e0);
  if (width == btor_node_bv_get_width (btor, e1))
  {
    res = translate_shift (btor, e0, e1, btor_exp_bv_sra);
  }
  else
  {
    BTOR_ABORT (!btor_util_is_power_of_2 (width),
                "bit-width of 'e0' must be a power of 2");
    BTOR_ABORT (btor_util_log_2 (width) != btor_node_bv_get_width (btor, e1),
                "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
    res = btor_exp_bv_sra (btor, e0, e1);
  }
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sra, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

// TODO (ma): allow width(n0) == width(n1)
BoolectorNode *
boolector_rol (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width;
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
  width = btor_node_bv_get_width (btor, e0);
  BTOR_ABORT (!btor_util_is_power_of_2 (width),
              "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT (btor_util_log_2 (width) != btor_node_bv_get_width (btor, e1),
              "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_exp_bv_rol (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, rol, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

// TODO (ma): allow width(n0) == width(n1)
BoolectorNode *
boolector_ror (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width;
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
  width = btor_node_bv_get_width (btor, e0);
  BTOR_ABORT (!btor_util_is_power_of_2 (width),
              "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT (btor_util_log_2 (width) != btor_node_bv_get_width (btor, e1),
              "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  res = btor_exp_bv_ror (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_sub (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_usubo (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_ssubo (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_udiv (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_sdiv (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_sdivo (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_urem (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_srem (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_SORT_MISMATCH (e0, e1);
  res = btor_exp_bv_smod (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT (btor_node_bv_get_width (btor, e0)
                  > UINT32_MAX - btor_node_bv_get_width (btor, e1),
              "bit-width of result is too large");
  res = btor_exp_bv_concat (btor, e0, e1);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, concat, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_repeat (Btor *btor, BoolectorNode *node, uint32_t n)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN_EXT (exp, "%u", n);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  BTOR_ABORT (
      ((uint32_t) (UINT32_MAX / n)) < btor_node_bv_get_width (btor, exp),
      "resulting bit-width of 'repeat' too large");
  res = btor_exp_bv_repeat (btor, exp, n);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, repeat, BTOR_CLONED_EXP (exp), n);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

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
  BTOR_ABORT_IS_NOT_ARRAY (e_array);
  BTOR_ABORT_IS_NOT_BV (e_index);
  BTOR_ABORT (
      btor_sort_array_get_index (btor, btor_node_get_sort_id (e_array))
          != btor_node_get_sort_id (e_index),
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  res = btor_exp_read (btor, e_array, e_index);
  btor_node_inc_ext_ref_counter (btor, res);
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
  BTOR_ABORT_IS_NOT_ARRAY (e_array);
  BTOR_ABORT_IS_NOT_BV (e_index);
  BTOR_ABORT_IS_NOT_BV (e_value);
  BTOR_ABORT (
      btor_sort_array_get_index (btor, btor_node_get_sort_id (e_array))
          != btor_node_get_sort_id (e_index),
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  BTOR_ABORT (
      btor_sort_array_get_element (btor, btor_node_get_sort_id (e_array))
          != btor_node_get_sort_id (e_value),
      "element bit-width of 'e_array' and bit-width of 'e_value' must be "
      "equal");
  res = btor_exp_write (btor, e_array, e_index, e_value);
  btor_node_inc_ext_ref_counter (btor, res);
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

/*------------------------------------------------------------------------*/

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
  BTOR_ABORT (btor_node_bv_get_width (btor, e_cond) != 1,
              "bit-width of 'e_cond' must be equal to 1");
  BTOR_ABORT (btor_node_get_sort_id (e_if) != btor_node_get_sort_id (e_else),
              "sorts of 'e_if' and 'e_else' branch must be equal");
  res = btor_exp_cond (btor, e_cond, e_if, e_else);
  btor_node_inc_ext_ref_counter (btor, res);
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

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_param (Btor *btor, BoolectorSort sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL (btor);

  BtorNode *res;
  char *symb;
  BtorSortId s;

  symb = mk_unique_symbol (btor, symbol);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT " %s", sort, btor, symb);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, s),
              "'sort' is not a bit vector sort");
  BTOR_ABORT (symb && btor_hashptr_table_get (btor->symbols, symb),
              "symbol '%s' is already in use in the current context",
              symb);
  res = btor_exp_param (btor, s, symb);
  btor_mem_freestr (btor->mm, symb);
  btor_node_inc_ext_ref_counter (btor, res);

  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, param, sort, symbol);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_fun (Btor *btor,
               BoolectorNode **param_nodes,
               uint32_t paramc,
               BoolectorNode *node)
{
  uint32_t i;
  BtorNode **params, *exp, *res;

  params = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (param_nodes);
  exp    = BTOR_IMPORT_BOOLECTOR_NODE (node);

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (params);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT (paramc < 1, "'paramc' must not be < 1");

  BTOR_TRAPI_PRINT ("%s %p %u ", __FUNCTION__ + 10, btor, paramc);
  for (i = 0; i < paramc; i++)
  {
    BTOR_ABORT (!params[i] || !btor_node_is_param (params[i]),
                "'params[%u]' is not a parameter",
                i);
    BTOR_ABORT (btor_node_param_is_bound (params[i]),
                "'params[%u]' already bound");
    BTOR_ABORT_REFS_NOT_POS (params[i]);
    BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (params[i]));
  }
  BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (exp));
  BTOR_TRAPI_PRINT ("\n");

  BTOR_ABORT (btor_node_is_uf (btor_simplify_exp (btor, exp)),
              "expected bit vector term as function body");
  res = btor_exp_fun (btor, params, paramc, exp);
  btor_node_inc_ext_ref_counter (btor, res);
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
                 uint32_t argc,
                 BoolectorNode *n_fun)
{
  uint32_t i;
  int32_t fcheck;
  BtorNode **args, *e_fun, *res;

  args  = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);
  e_fun = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e_fun);

  BTOR_ABORT_REFS_NOT_POS (e_fun);
  BTOR_ABORT_BTOR_MISMATCH (btor, e_fun);

  BTOR_TRAPI_PRINT ("%s %p %u ", __FUNCTION__ + 10, btor, argc);
  for (i = 0; i < argc; i++)
    BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
  BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (e_fun));
  BTOR_TRAPI_PRINT ("\n");

  BTOR_ABORT (!btor_sort_is_fun (btor, btor_node_get_sort_id (e_fun)),
              "'e_fun' must be a function");
  BTOR_ABORT (
      (uint32_t) argc != btor_node_fun_get_arity (btor, e_fun),
      "number of arguments must be equal to the number of parameters in "
      "'e_fun'");
  BTOR_ABORT (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT (argc >= 1 && !args, "no arguments given but argc defined > 0");
  fcheck = btor_fun_sort_check (btor, args, argc, e_fun);
  BTOR_ABORT (fcheck >= 0, "invalid argument given at position %d", fcheck);
  res = btor_exp_apply_n (btor, e_fun, args, argc);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES_PTR (res, apply, carg_nodes, argc, BTOR_CLONED_EXP (e_fun));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

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

  res = btor_exp_bv_inc (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
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

  res = btor_exp_bv_dec (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, dec, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

static bool
params_distinct (Btor *btor, BtorNode *params[], uint32_t paramc)
{
  bool res                = true;
  BtorIntHashTable *cache = btor_hashint_table_new (btor->mm);
  for (uint32_t i = 0; i < paramc; i++)
  {
    if (btor_hashint_table_contains (cache, btor_node_get_id (params[i])))
    {
      res = false;
      break;
    }
    btor_hashint_table_add (cache, btor_node_get_id (params[i]));
  }
  btor_hashint_table_delete (cache);
  return res;
}

BoolectorNode *
boolector_forall (Btor *btor,
                  BoolectorNode *param_nodes[],
                  uint32_t paramc,
                  BoolectorNode *body_node)
{
  uint32_t i;
  BtorNode **params, *body, *res;

  params = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (param_nodes);
  body   = BTOR_IMPORT_BOOLECTOR_NODE (body_node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (params);
  BTOR_ABORT_ARG_NULL (body);

  BTOR_TRAPI_PRINT ("%s %p %u ", __FUNCTION__ + 10, btor, paramc);
  for (i = 0; i < paramc; i++)
  {
    BTOR_ABORT (!params[i] || !btor_node_is_param (params[i]),
                "'params[%u]' is not a parameter",
                i);
    BTOR_ABORT (btor_node_param_is_bound (params[i]),
                "'params[%u]' already bound");
    BTOR_ABORT_REFS_NOT_POS (params[i]);
    BTOR_ABORT_BTOR_MISMATCH (btor, params[i]);
    BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (params[i]));
  }
  BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (body));
  BTOR_TRAPI_PRINT ("\n");
  BTOR_ABORT (!params_distinct (btor, params, paramc),
              "given parameters are not distinct");

  BTOR_ABORT_REFS_NOT_POS (body);
  BTOR_ABORT_BTOR_MISMATCH (btor, body);
  BTOR_ABORT (!btor_sort_is_bool (btor, btor_node_real_addr (body)->sort_id),
              "body of forall must be bit width 1, but has "
              "%u instead",
              btor_node_bv_get_width (btor, body));

  res = btor_exp_forall_n (btor, params, paramc, body);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BoolectorNode *cparam_nodes[paramc];
  for (i = 0; btor->clone && i < paramc; i++)
    cparam_nodes[i] = BTOR_CLONED_EXP (params[i]);
  BTOR_CHKCLONE_RES_PTR (
      res, forall, cparam_nodes, paramc, BTOR_CLONED_EXP (body));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_exists (Btor *btor,
                  BoolectorNode *param_nodes[],
                  uint32_t paramc,
                  BoolectorNode *body_node)
{
  uint32_t i;
  BtorNode **params, *body, *res;

  params = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (param_nodes);
  body   = BTOR_IMPORT_BOOLECTOR_NODE (body_node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (params);
  BTOR_ABORT_ARG_NULL (body);

  BTOR_TRAPI_PRINT ("%s %p %u ", __FUNCTION__ + 10, btor, paramc);
  for (i = 0; i < paramc; i++)
  {
    BTOR_ABORT (!params[i] || !btor_node_is_param (params[i]),
                "'params[%u]' is not a parameter",
                i);
    BTOR_ABORT (btor_node_param_is_bound (params[i]),
                "'params[%u]' already bound");
    BTOR_ABORT_REFS_NOT_POS (params[i]);
    BTOR_ABORT_BTOR_MISMATCH (btor, params[i]);
    BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (params[i]));
  }
  BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (body));
  BTOR_TRAPI_PRINT ("\n");
  BTOR_ABORT (!params_distinct (btor, params, paramc),
              "given parameters are not distinct");

  BTOR_ABORT_REFS_NOT_POS (body);
  BTOR_ABORT_BTOR_MISMATCH (btor, body);
  BTOR_ABORT (!btor_sort_is_bool (btor, btor_node_real_addr (body)->sort_id),
              "body of exists must be bit width 1, but has "
              "%u instead",
              btor_node_bv_get_width (btor, body));

  res = btor_exp_exists_n (btor, params, paramc, body);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BoolectorNode *cparam_nodes[paramc];
  for (i = 0; btor->clone && i < paramc; i++)
    cparam_nodes[i] = BTOR_CLONED_EXP (params[i]);
  BTOR_CHKCLONE_RES_PTR (
      res, exists, cparam_nodes, paramc, BTOR_CLONED_EXP (body));
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
  real_exp = btor_node_real_addr (exp);
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
boolector_get_node_id (Btor *btor, BoolectorNode *node)
{
  int32_t res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (node);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  res = btor_node_get_id (btor_node_real_addr (exp));
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_INT (res, get_node_id, BTOR_CLONED_EXP (exp));
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
  res = btor_node_get_sort_id (exp);
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
  BTOR_ABORT (!btor_node_is_fun (btor_simplify_exp (btor, exp)),
              "node must be a function node");
  BTOR_TRAPI_UNFUN (exp);
  res = ((BtorFunSort) btor_sort_get_by_id (btor, btor_node_get_sort_id (exp))
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
  BTOR_ABORT (!btor_node_is_fun (btor_simplify_exp (btor, exp)),
              "node must be a function node");
  BTOR_TRAPI_UNFUN (exp);
  res = ((BtorFunSort) btor_sort_get_by_id (btor, btor_node_get_sort_id (exp))
             ->fun)
            .codomain->id;
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, fun_get_codomain_sort, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_match_node_by_id (Btor *btor, int32_t id)
{
  BtorNode *res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (id <= 0, "node id must be > 0");
  BTOR_TRAPI ("%d", id);
  res = btor_node_match_by_id (btor, id);
  BTOR_ABORT (!res, "invalid node id '%d', node does not exist", id);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, match_node_by_id, id);
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_match_node_by_symbol (Btor *btor, const char *symbol)
{
  char *symb;
  BtorNode *res;
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (symbol);
  BTOR_TRAPI ("%s", symbol);
  symb = mk_unique_symbol (btor, symbol);
  res  = btor_node_match_by_symbol (btor, symb);
  btor_mem_freestr (btor->mm, symb);
  btor_node_inc_ext_ref_counter (btor, res);
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
  res = btor_node_match (btor, exp);
  btor_node_inc_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_NODE (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, match_node, BTOR_CLONED_EXP (exp));
#endif
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

/*------------------------------------------------------------------------*/

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
  res = remove_unique_symbol_prefix (btor, btor_node_get_symbol (btor, exp));
  BTOR_TRAPI_RETURN_STR (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_STR (res, get_symbol, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

void
boolector_set_symbol (Btor *btor, BoolectorNode *node, const char *symbol)
{
  char *symb;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_ABORT_ARG_NULL (symbol);
  BTOR_TRAPI_UNFUN_EXT (exp, "%s", symbol);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  symb = mk_unique_symbol (btor, symbol);
  btor_node_set_symbol (btor, exp, symb);
  btor_mem_freestr (btor->mm, symb);
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
  if (btor_sort_is_fun (btor, btor_node_get_sort_id (exp)))
    res = btor_node_fun_get_width (btor, exp);
  else
    res = btor_node_bv_get_width (btor, exp);
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
  BTOR_ABORT_IS_NOT_ARRAY (e_array);
  BTOR_ABORT (btor_node_fun_get_arity (btor, e_array) > 1,
              "'n_array' is a function with arity > 1");
  res = btor_node_array_get_index_width (btor, e_array);
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
  BTOR_ABORT (!btor_node_is_bv_const (exp), "argument is not a constant node");
  real = btor_node_real_addr (exp);
  /* representations of bits of const nodes are maintained analogously
   * to bv assignment strings */
  if (!btor_node_is_inverted (exp))
    bits = btor_bv_to_char (btor->mm, btor_node_bv_const_get_bits (exp));
  else
    bits = btor_bv_to_char (btor->mm, btor_node_bv_const_get_invbits (real));
  bvass = btor_ass_new_bv (btor->bv_assignments, bits);
  btor_mem_freestr (btor->mm, bits);
  res = btor_ass_get_bv_str (bvass);
  BTOR_TRAPI_RETURN_PTR (res);
#ifndef NDEBUG
  if (btor->clone)
  {
    const char *cloneres =
        boolector_get_bits (btor->clone, BTOR_CLONED_EXP (exp));
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
  BTOR_ABORT (!btor_node_is_fun (btor_simplify_exp (btor, exp)),
              "given expression is not a function node");
  res = btor_node_fun_get_arity (btor, exp);
  BTOR_TRAPI_RETURN_UINT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_UINT (res, get_fun_arity, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

/*------------------------------------------------------------------------*/

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
  res = btor_node_is_bv_const (exp);
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
  res = btor_node_is_bv_var (btor_simplify_exp (btor, exp));
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
  res = btor_node_is_array (btor_simplify_exp (btor, exp));
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
  res = btor_node_is_uf_array (btor_simplify_exp (btor, exp));
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
  res = btor_node_is_param (btor_simplify_exp (btor, exp));
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
  BTOR_ABORT (!btor_node_is_param (btor_simplify_exp (btor, exp)),
              "given expression is not a parameter node");
  res = btor_node_param_is_bound (exp);
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
  res = btor_node_is_uf (btor_simplify_exp (btor, exp));
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
  res = btor_node_is_fun (btor_simplify_exp (btor, exp));
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_fun, BTOR_CLONED_EXP (exp));
#endif
  return res;
}

/*------------------------------------------------------------------------*/

int32_t
boolector_fun_sort_check (Btor *btor,
                          BoolectorNode **arg_nodes,
                          uint32_t argc,
                          BoolectorNode *n_fun)
{
  BtorNode **args, *e_fun;
  uint32_t i;
  int32_t res;

  args  = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);
  e_fun = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (e_fun);
  BTOR_ABORT (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT (argc >= 1 && !args, "no arguments given but argc defined > 0");

  BTOR_TRAPI_PRINT ("%s %p %u ", __FUNCTION__ + 10, btor, argc);
  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_ARG_NULL (args[i]);
    BTOR_ABORT_REFS_NOT_POS (args[i]);
    BTOR_ABORT_BTOR_MISMATCH (btor, args[i]);
    BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
  }
  BTOR_TRAPI_PRINT (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (e_fun));
  BTOR_TRAPI_PRINT ("\n");

  res = btor_fun_sort_check (btor, args, argc, e_fun);
  BTOR_TRAPI_RETURN_INT (res);
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES_INT (
      res, fun_sort_check, carg_nodes, argc, BTOR_CLONED_EXP (e_fun));
#endif
  return res;
}

/*------------------------------------------------------------------------*/

const char *
boolector_bv_assignment (Btor *btor, BoolectorNode *node)
{
  char *ass;
  const char *res;
  BtorNode *exp;
  BtorBVAss *bvass;
  uint32_t opt;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT (btor->last_sat_result != BTOR_RESULT_SAT,
              "cannot retrieve model if input formula is not SAT");
  BTOR_ABORT (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN),
              "model generation has not been enabled");
  BTOR_ABORT (btor->quantifiers->count,
              "models are currently not supported with quantifiers");
  BTOR_ABORT_ARG_NULL (exp);
  BTOR_TRAPI_UNFUN (exp);
  BTOR_ABORT_REFS_NOT_POS (exp);
  BTOR_ABORT_BTOR_MISMATCH (btor, exp);
  BTOR_ABORT_IS_NOT_BV (exp);
  opt = btor_opt_get (btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT);
  switch (opt)
  {
    case BTOR_OUTPUT_BASE_HEX:
      ass = btor_bv_to_hex_char (btor->mm, btor_model_get_bv (btor, exp));
      break;
    case BTOR_OUTPUT_BASE_DEC:
      ass = btor_bv_to_dec_char (btor->mm, btor_model_get_bv (btor, exp));
      break;
    default:
      assert (opt == BTOR_OUTPUT_BASE_BIN);
      ass = btor_bv_to_char (btor->mm, btor_model_get_bv (btor, exp));
  }
  bvass = btor_ass_new_bv (btor->bv_assignments, ass);
  btor_mem_freestr (btor->mm, ass);
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
    Btor *btor, BtorNode *exp, char ***args, char ***values, uint32_t *size)
{
  assert (btor);
  assert (exp);
  assert (args);
  assert (values);
  assert (size);
  assert (btor_node_is_regular (exp));

  char *arg, *tmp, *bv;
  uint32_t i, j, len;
  BtorPtrHashTableIterator it;
  const BtorPtrHashTable *model;
  BtorBitVector *value;
  BtorBitVectorTuple *t;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_node_is_fun (exp));

  model = btor_model_get_fun_aux (btor, btor->bv_model, btor->fun_model, exp);

  if ((btor_node_is_lambda (exp) && btor_node_fun_get_arity (btor, exp) > 1)
      || !btor->fun_model || !model)
  {
    *size = 0;
    return;
  }

  assert (model->count > 0);

  *size = model->count;
  BTOR_NEWN (btor->mm, *args, *size);
  BTOR_NEWN (btor->mm, *values, *size);

  i = 0;
  btor_iter_hashptr_init (&it, (BtorPtrHashTable *) model);
  while (btor_iter_hashptr_has_next (&it))
  {
    value = (BtorBitVector *) it.bucket->data.as_ptr;

    /* build assignment string for all arguments */
    t   = (BtorBitVectorTuple *) btor_iter_hashptr_next (&it);
    len = t->arity;
    for (j = 0; j < t->arity; j++) len += t->bv[j]->width;
    BTOR_NEWN (btor->mm, arg, len);
    tmp = arg;

    bv = btor_bv_to_char (btor->mm, t->bv[0]);
    strcpy (tmp, bv);
    btor_mem_freestr (btor->mm, bv);

    for (j = 1; j < t->arity; j++)
    {
      bv = btor_bv_to_char (btor->mm, t->bv[j]);
      strcat (tmp, " ");
      strcat (tmp, bv);
      btor_mem_freestr (btor->mm, bv);
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
                uint32_t *size,
                BtorFunAss **ass)
{
  assert (btor);
  assert (n);
  assert (args);
  assert (values);
  assert (size);
  assert (btor_node_is_regular (n));

  uint32_t i;
  char **a = 0, **v = 0;

  *ass = 0;
  generate_fun_model_str (btor, n, &a, &v, size);

  if (*size)
  {
    *ass = btor_ass_new_fun (btor->fun_assignments, a, v, *size);
    for (i = 0; i < *size; i++)
    {
      btor_mem_freestr (btor->mm, a[i]);
      btor_mem_freestr (btor->mm, v[i]);
    }
    btor_mem_free (btor->mm, a, *size * sizeof (*a));
    btor_mem_free (btor->mm, v, *size * sizeof (*v));
    btor_ass_get_fun_indices_values (*ass, args, values, *size);
  }
}

void
boolector_array_assignment (Btor *btor,
                            BoolectorNode *n_array,
                            char ***indices,
                            char ***values,
                            uint32_t *size)
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
  BTOR_ABORT_IS_NOT_ARRAY (e_array);

  fun_assignment (btor, e_array, indices, values, size, &ass);

  /* special case: we treat out parameters as return values for btoruntrace */
  BTOR_TRAPI_RETURN ("%p %p %u", *indices, *values, *size);

#ifndef NDEBUG
  if (btor->clone)
  {
    char **cindices, **cvalues;
    uint32_t i, csize;
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
                                 uint32_t size)
{
  BtorFunAss *funass;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%p %p %u", indices, values, size);
  BTOR_ABORT (size && !indices, "size > 0 but 'indices' are zero");
  BTOR_ABORT (size && !values, "size > 0 but 'values' are zero");
  BTOR_ABORT (!size && indices, "non zero 'indices' but 'size == 0'");
  BTOR_ABORT (!size && values, "non zero 'values' but 'size == 0'");
  if (!size) { return; }

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
boolector_uf_assignment (Btor *btor,
                         BoolectorNode *n_uf,
                         char ***args,
                         char ***values,
                         uint32_t *size)
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
  BTOR_ABORT_IS_NOT_FUN (e_uf);

  fun_assignment (btor, e_uf, args, values, size, &ass);

  /* special case: we treat out parameters as return values for btoruntrace */
  BTOR_TRAPI_RETURN ("%p %p %u", *args, *values, *size);

#ifndef NDEBUG
  if (btor->clone)
  {
    char **cargs, **cvalues;
    uint32_t i, csize;
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
boolector_free_uf_assignment (Btor *btor,
                              char **args,
                              char **values,
                              uint32_t size)
{
  BtorFunAss *funass;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%p %p %u", args, values, size);
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
  BTOR_ABORT (btor->quantifiers->count,
              "models are currently not supported with quantifiers");
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
  res = btor_sort_bool (btor);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, bool_sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort
boolector_bitvec_sort (Btor *btor, uint32_t width)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI ("%u", width);
  BTOR_ABORT (width == 0, "'width' must be > 0");

  BtorSortId res;
  res = btor_sort_bv (btor, width);
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
  return btor_sort_tuple (btor, element_ids, num_elements);
}

BoolectorSort
boolector_fun_sort (Btor *btor,
                    BoolectorSort domain[],
                    uint32_t arity,
                    BoolectorSort codomain)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (domain);
  BTOR_ABORT (arity <= 0, "'arity' must be > 0");

  uint32_t i;
  BtorSortId res, tup, cos, s;

  BTOR_TRAPI_PRINT ("%s %p ", __FUNCTION__ + 10, btor);
  BTOR_TRAPI_PRINT (
      BTOR_TRAPI_SORT_FMT, BTOR_IMPORT_BOOLECTOR_SORT ((domain[0])), btor);
  for (i = 1; i < arity; i++)
    BTOR_TRAPI_PRINT (
        BTOR_TRAPI_SORT_FMT, BTOR_IMPORT_BOOLECTOR_SORT (domain[i]), btor);
  BTOR_TRAPI_PRINT (
      BTOR_TRAPI_SORT_FMT, BTOR_IMPORT_BOOLECTOR_SORT (codomain), btor);
  BTOR_TRAPI_PRINT ("\n");

  for (i = 0; i < arity; i++)
  {
    s = BTOR_IMPORT_BOOLECTOR_SORT (domain[i]);
    BTOR_ABORT (!btor_sort_is_valid (btor, s),
                "'domain' sort at position %u is not a valid sort",
                i);
    BTOR_ABORT (
        !btor_sort_is_bv (btor, s) && !btor_sort_is_bool (btor, s),
        "'domain' sort at position %u must be a bool or bit vector sort",
        i);
  }
  cos = BTOR_IMPORT_BOOLECTOR_SORT (codomain);
  BTOR_ABORT (!btor_sort_is_valid (btor, cos),
              "'codomain' sort is not a valid sort");
  BTOR_ABORT (
      !btor_sort_is_bv (btor, cos) && !btor_sort_is_bool (btor, cos),
      "'codomain' sort must be a bool or bit vector sort");

  tup = boolector_tuple_sort (btor, domain, arity);

  res = btor_sort_fun (btor, tup, cos);
  btor_sort_release (btor, tup);
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
  BTOR_TRAPI (
      BTOR_TRAPI_SORT_FMT " " BTOR_TRAPI_SORT_FMT, index, btor, element, btor);

  BtorSortId is, es, res;

  is = BTOR_IMPORT_BOOLECTOR_SORT (index);
  es = BTOR_IMPORT_BOOLECTOR_SORT (element);

  BTOR_ABORT (!btor_sort_is_valid (btor, is),
              "'index' sort is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, is),
              "'index' is not a bit vector sort");
  BTOR_ABORT (!btor_sort_is_valid (btor, es),
              "'element' sort is not a valid sort");
  BTOR_ABORT (!btor_sort_is_bv (btor, es),
              "'element' is not a bit vector sort");

  res = btor_sort_array (btor, is, es);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, array_sort, index, element);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

BoolectorSort
boolector_copy_sort (Btor *btor, BoolectorSort sort)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, BTOR_IMPORT_BOOLECTOR_SORT (sort), btor);

  BtorSortId s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  BtorSortId res = btor_sort_copy (btor, s);
  inc_sort_ext_ref_counter (btor, res);
  BTOR_TRAPI_RETURN_SORT (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_SORT (res, copy_sort, sort);
#endif
  return BTOR_EXPORT_BOOLECTOR_SORT (res);
}

void
boolector_release_sort (Btor *btor, BoolectorSort sort)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, BTOR_IMPORT_BOOLECTOR_SORT (sort), btor);

  BtorSortId s = BTOR_IMPORT_BOOLECTOR_SORT (sort);
  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");
  dec_sort_ext_ref_counter (btor, s);
  btor_sort_release (btor, s);
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
  res = btor_node_get_sort_id (e0) == btor_node_get_sort_id (e1);
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
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);

  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");

  res = btor_sort_is_array (btor, s);
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
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);

  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");

  res = btor_sort_is_bv (btor, s);
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
  BTOR_TRAPI (BTOR_TRAPI_SORT_FMT, sort, btor);
  s = BTOR_IMPORT_BOOLECTOR_SORT (sort);

  BTOR_ABORT (!btor_sort_is_valid (btor, s), "'sort' is not a valid sort");

  res = btor_sort_is_fun (btor, s);
  BTOR_TRAPI_RETURN_BOOL (res);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_BOOL (res, is_fun_sort, sort);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

/* Note: no need to trace parse function calls!! */

int32_t
boolector_parse (Btor *btor,
                 FILE *infile,
                 const char *infile_name,
                 FILE *outfile,
                 char **error_msg,
                 int32_t *status)
{
  int32_t res;

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

int32_t
boolector_parse_btor (Btor *btor,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      int32_t *status)
{
  int32_t res;

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

int32_t
boolector_parse_btor2 (Btor *btor,
                       FILE *infile,
                       const char *infile_name,
                       FILE *outfile,
                       char **error_msg,
                       int32_t *status)
{
  int32_t res;

  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (infile);
  BTOR_ABORT_ARG_NULL (infile_name);
  BTOR_ABORT_ARG_NULL (outfile);
  BTOR_ABORT_ARG_NULL (error_msg);
  BTOR_ABORT_ARG_NULL (status);
  BTOR_ABORT (BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
              "file parsing must be done before creating expressions");
  res = btor_parse_btor2 (btor, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

int32_t
boolector_parse_smt1 (Btor *btor,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      int32_t *status)
{
  int32_t res;

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

int32_t
boolector_parse_smt2 (Btor *btor,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      int32_t *status)
{
  int32_t res;

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
  btor_dumpbtor_dump_node (btor, file, btor_simplify_exp (btor, exp));
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
  BTOR_ABORT (!btor_dumpbtor_can_be_dumped (btor),
              "formula cannot be dumped in BTOR format as it does "
              "not support uninterpreted functions yet.");
  BTOR_WARN (btor->assumptions->count > 0,
             "dumping in incremental mode only captures the current state "
             "of the input formula without assumptions");
  btor_dumpbtor_dump (btor, file, 1);
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
  btor_dumpbtor_dump (btor, file, 2);
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
  btor_dumpsmt_dump_node (btor, file, btor_simplify_exp (btor, exp), 0);
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
  btor_dumpsmt_dump (btor, file);
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
  btor_dumpaig_dump (btor, false, file, merge_roots);
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
  btor_dumpaig_dump (btor, true, file, merge_roots);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_aiger_binary, stdout, merge_roots);
#endif
}

/*------------------------------------------------------------------------*/

const char *
boolector_copyright (Btor *btor)
{
  /* do not trace, not necessary */
  BTOR_ABORT_ARG_NULL (btor);
  return "This software is\n"
         "Copyright (c) 2007-2009 Robert Brummayer\n"
         "Copyright (c) 2007-2018 Armin Biere\n"
         "Copyright (c) 2012-2018 Aina Niemetz, Mathias Preiner\n"
#ifdef BTOR_USE_LINGELING
         "\n"
         "This software is linked against Lingeling\n"
         "Copyright (c) 2010-2018 Armin Biere\n"
#endif
#ifdef BTOR_USE_PICOSAT
         "\n"
         "This software is linked against PicoSAT\n"
         "Copyright (c) 2006-2016 Armin Biere\n"
#endif
#ifdef BTOR_USE_MINISAT
         "\n"
         "This software is linked against MiniSAT\n"
         "Copyright (c) 2003-2013, Niklas Een, Niklas Sorensson\n"
#endif
#ifdef BTOR_USE_CADICAL
         "\n"
         "This software is linked against CaDiCaL\n"
         "Copyright (c) 2016-2018 Armin Biere\n"
#endif
         "";
}

const char *
boolector_version (Btor *btor)
{
  /* do not trace, not necessary */
  BTOR_ABORT_ARG_NULL (btor);
  return btor_version (btor);
}

const char *
boolector_git_id (Btor *btor)
{
  /* do not trace, not necessary */
  BTOR_ABORT_ARG_NULL (btor);
  return btor_git_id (btor);
}

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012 Mathias Preiner.
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/

#include "boolector.h"
#include "btorabort.h"
#include "btordump.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btorutil.h"

/*------------------------------------------------------------------------*/

#include <limits.h>
#include <stdio.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#define BTOR_TRAPI(msg, args...)    \
  do                                \
  {                                 \
    if (!btor->apitrace) break;     \
    btor_trapi (btor, msg, ##args); \
  } while (0)

#define BTOR_TRAPI_RETURN(res)     \
  do                               \
  {                                \
    BTOR_TRAPI ("return %d", res); \
  } while (0)

#define BTOR_TRAPI_RETURNP(res)    \
  do                               \
  {                                \
    BTOR_TRAPI ("return %p", res); \
  } while (0)

#define BTOR_TRAPI_RETURNS(res)    \
  do                               \
  {                                \
    BTOR_TRAPI ("return %s", res); \
  } while (0)

static void
btor_trapi (Btor *btor, const char *msg, ...)
{
  assert (btor);
  assert (btor->apitrace);

  va_list args;

  va_start (args, msg);
  vfprintf (btor->apitrace, msg, args);
  va_end (args);
  fputc ('\n', btor->apitrace);
  fflush (btor->apitrace);
}

static void
btor_open_apitrace (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);

  FILE *file;
  char *cmd;
  int len = strlen (name);

  if (len >= 3 && !strcmp (name + len - 3, ".gz"))
  {
    len += 20;
    BTOR_NEWN (btor->mm, cmd, len);
    sprintf (cmd, "gzip -c > %s", name);
    if ((file = popen (cmd, "w"))) btor->closeapitrace = 2;
    BTOR_DELETEN (btor->mm, cmd, len);
  }
  else
  {
    if ((file = fopen (name, "w"))) btor->closeapitrace = 1;
  }

  if (file)
    btor->apitrace = file;
  else
    printf ("[boolector] WARNING failed to write API trace file to '%s'", name);
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
  // TODO TRAPI
  return btor_clone_btor (btor);
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
}

void
boolector_generate_model_for_all_reads (Btor *btor)
{
  // TODO TRAPI
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  btor_generate_model_for_all_reads (btor);
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
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_get_refs (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("get_refs");
  res = btor->external_refs;
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
  btor_delete_btor (btor);
}

BtorNode *
boolector_const (Btor *btor, const char *bits)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("const %s", bits);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (bits);
  BTOR_ABORT_BOOLECTOR (*bits == '\0', "'bits' must not be empty");
  btor->external_refs++;
  res = btor_const_exp (btor, bits);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_zero (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("zero %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_zero_exp (btor, width);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_false (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("false");
  btor->external_refs++;
  res = btor_false_exp (btor);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_ones (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ones %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_ones_exp (btor, width);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_true (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("true");
  btor->external_refs++;
  res = btor_true_exp (btor);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_one (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("one %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_one_exp (btor, width);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_unsigned_int (Btor *btor, unsigned int u, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("unsigned_int %u %d", u, width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_unsigned_to_exp (btor, u, width);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_int (Btor *btor, int i, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("int %d %u", i, width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_int_to_exp (btor, i, width);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
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

  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_array (Btor *btor,
                 int elem_width,
                 int index_width,
                 const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  BtorNode *res;
  char *symb;

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

  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_not (Btor *btor, BtorNode *exp)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("not %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  res = btor_not_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_neg (Btor *btor, BtorNode *exp)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("neg %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  res = btor_neg_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_redor (Btor *btor, BtorNode *exp)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("redor %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  res = btor_redor_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_redxor (Btor *btor, BtorNode *exp)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("redxor %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  res = btor_redxor_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_redand (Btor *btor, BtorNode *exp)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("redand %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  res = btor_redand_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_slice (Btor *btor, BtorNode *exp, int upper, int lower)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("slice %p %d %d", exp, upper, lower);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (lower < 0, "'lower' must not be negative");
  BTOR_ABORT_BOOLECTOR (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT_BOOLECTOR (upper >= BTOR_REAL_ADDR_NODE (exp)->len,
                        "'upper' must not be >= width of 'exp'");
  btor->external_refs++;
  res = btor_slice_exp (btor, exp, upper, lower);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_uext (Btor *btor, BtorNode *exp, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("uext %p %d", exp, width);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  res = btor_uext_exp (btor, exp, width);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_sext (Btor *btor, BtorNode *exp, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sext %p %d", exp, width);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  res = btor_sext_exp (btor, exp, width);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_implies (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("implies %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_NODE (e0)->len != 1 || BTOR_REAL_ADDR_NODE (e1)->len != 1,
      "bit-width of 'e0' and 'e1' have be 1");
  btor->external_refs++;
  res = btor_implies_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_iff (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("iff %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_NODE (e0)->len != 1 || BTOR_REAL_ADDR_NODE (e1)->len != 1,
      "bit-width of 'e0' and 'e1' must not be unequal to 1");
  btor->external_refs++;
  res = btor_iff_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_xor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("xor %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_xor_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_xnor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("xnor %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_xnor_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("and %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_and_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_nand (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("nand %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_nand_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_or (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("or %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_or_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_nor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("nor %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_nor_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1, *res;
  int is_array_e0, is_array_e1;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("eq %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0          = btor_simplify_exp (btor, e0);
  e1          = btor_simplify_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_NODE (e0);
  real_e1     = BTOR_REAL_ADDR_NODE (e1);
  is_array_e0 = BTOR_IS_ARRAY_NODE (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_NODE (real_e1);
  BTOR_ABORT_BOOLECTOR (is_array_e0 != is_array_e1,
                        "array must not be compared to bit-vector");
  BTOR_ABORT_BOOLECTOR (
      !is_array_e0 && real_e0 && real_e1 && real_e0->len != real_e1->len,
      "bit-vectors must not have unequal bit-width");
  BTOR_ABORT_BOOLECTOR (
      is_array_e0 && real_e0 && real_e1 && real_e0->len != real_e1->len,
      "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0 && real_e1
                            && real_e0->index_len != real_e1->index_len,
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  res = btor_eq_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_ne (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1, *res;
  int is_array_e0, is_array_e1;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ne %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0          = btor_simplify_exp (btor, e0);
  e1          = btor_simplify_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_NODE (e0);
  real_e1     = BTOR_REAL_ADDR_NODE (e1);
  is_array_e0 = BTOR_IS_ARRAY_NODE (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_NODE (real_e1);
  BTOR_ABORT_BOOLECTOR (is_array_e0 != is_array_e1,
                        "array must not be compared to bit-vector");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->len != real_e1->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->index_len != real_e1->index_len,
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  res = btor_ne_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("add %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_add_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_uaddo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("uaddo %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_uaddo_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_saddo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("saddo %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_saddo_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("mul %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_mul_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_umulo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("umulo %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_umulo_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_smulo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("smulo %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_smulo_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ult %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_ult_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_slt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("slt %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_slt_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_ulte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ulte %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_ulte_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_slte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("slte %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_slte_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_ugt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ugt %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_ugt_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_sgt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sgt %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_sgt_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_ugte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ugte %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_ugte_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_sgte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sgte %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_sgte_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_sll (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sll %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_NODE (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_sll_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_srl (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("srl %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_NODE (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_srl_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_sra (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sra %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_NODE (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_sra_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_rol (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("rol %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_NODE (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_rol_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_ror (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ror %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_NODE (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_ror_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_sub (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sub %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_sub_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_usubo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("usubo %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_usubo_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_ssubo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ssubo %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_ssubo_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("udiv %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_udiv_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_sdiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sdiv %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_sdiv_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_sdivo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sdivo %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_sdivo_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("urem %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_urem_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_srem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("srem %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_srem_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_smod (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("smod %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  res = btor_smod_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("concat %p %p", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_NODE (e0)->len > INT_MAX - BTOR_REAL_ADDR_NODE (e1)->len,
      "bit-width of result is too large");
  btor->external_refs++;
  res = btor_concat_exp (btor, e0, e1);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_read (Btor *btor, BtorNode *e_array, BtorNode *e_index)
{
  BtorNode *res;

  BTOR_TRAPI ("read %p %p", e_array, e_index);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_index);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_index);
  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  BTOR_ABORT_BV_BOOLECTOR (e_array);
  BTOR_ABORT_ARRAY_BOOLECTOR (e_index);
  BTOR_ABORT_BOOLECTOR (
      e_array->index_len != BTOR_REAL_ADDR_NODE (e_index)->len,
      "index bit-width of 'e_array' and bit-width of 'e_index' must not be "
      "unequal");
  btor->external_refs++;
  res = btor_read_exp (btor, e_array, e_index);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_write (Btor *btor,
                 BtorNode *e_array,
                 BtorNode *e_index,
                 BtorNode *e_value)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("write %p %p %p", e_array, e_index, e_value);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_index);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_value);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_index);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_value);
  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  e_value = btor_simplify_exp (btor, e_value);
  BTOR_ABORT_BV_BOOLECTOR (e_array);
  BTOR_ABORT_ARRAY_BOOLECTOR (e_index);
  BTOR_ABORT_ARRAY_BOOLECTOR (e_value);
  BTOR_ABORT_BOOLECTOR (
      e_array->index_len != BTOR_REAL_ADDR_NODE (e_index)->len,
      "index bit-width of 'e_array' and bit-width of 'e_index' must not be "
      "unequal");
  BTOR_ABORT_BOOLECTOR (e_array->len != BTOR_REAL_ADDR_NODE (e_value)->len,
                        "element bit-width of 'e_array' and bit-width of "
                        "'e_value' must not be unequal");
  btor->external_refs++;
  res = btor_write_exp (btor, e_array, e_index, e_value);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_cond (Btor *btor, BtorNode *e_cond, BtorNode *e_if, BtorNode *e_else)
{
  BtorNode *real_e_if, *real_e_else, *res;
  int is_array_e_if, is_array_e_else;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("cond %p %p %p", e_cond, e_if, e_else);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_cond);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_if);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_else);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_cond);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_if);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_else);
  e_cond = btor_simplify_exp (btor, e_cond);
  e_if   = btor_simplify_exp (btor, e_if);
  e_else = btor_simplify_exp (btor, e_else);
  BTOR_ABORT_ARRAY_BOOLECTOR (e_cond);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (e_cond)->len != 1,
                        "bit-width of 'e_cond' must be equal to 1");
  real_e_if       = BTOR_REAL_ADDR_NODE (e_if);
  real_e_else     = BTOR_REAL_ADDR_NODE (e_else);
  is_array_e_if   = BTOR_IS_ARRAY_NODE (real_e_if);
  is_array_e_else = BTOR_IS_ARRAY_NODE (real_e_else);
  BTOR_ABORT_BOOLECTOR (is_array_e_if != is_array_e_else,
                        "array must not be combined with bit-vector");
  BTOR_ABORT_BOOLECTOR (!is_array_e_if && real_e_if && real_e_else
                            && real_e_if->len != real_e_else->len,
                        "bit-vectors must not have unequal bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_e_if && real_e_if && real_e_else
                            && real_e_if->len != real_e_else->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_e_if && real_e_if && real_e_else
                            && real_e_if->index_len != real_e_else->index_len,
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  res = btor_cond_exp (btor, e_cond, e_if, e_else);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_lambda (Btor *btor, BtorNode *param, BtorNode *exp)
{
  // TODO TRAPI
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (param);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (param);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)),
                        "'param' must be a parameter");
  btor->external_refs++;
  return btor_lambda_exp (btor, param, exp);
}

BtorNode *
boolector_param (Btor *btor, int width, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  BtorNode *res;
  char *symb;

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

  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_fun (Btor *btor, int paramc, BtorNode **params, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (params);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (paramc < 1, "'paramc' must not be < 1");

  int i, len;
  char *strtrapi;
  BtorNode *res;

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
    sprintf (strtrapi + strlen (strtrapi), " %p", params[i]);
  }
  sprintf (strtrapi + strlen (strtrapi), " %p", exp);
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  btor->external_refs++;
  res = btor_fun_exp (btor, paramc, params, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

// TODO: allow partial application?
BtorNode *
boolector_apply (Btor *btor, int argc, BtorNode **args, BtorNode *fun)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (fun);
  BTOR_ABORT_BOOLECTOR (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT_BOOLECTOR (argc >= 1 && !args,
                        "no arguments given but argc defined > 0");

  // TODO: get arity of function
  int i, len;
  char *strtrapi;
  BtorNode *res, *cur;

  len = 7 + 10 + argc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "apply %d", argc);

  cur = BTOR_REAL_ADDR_NODE (fun);
  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_BOOLECTOR (
        !BTOR_IS_LAMBDA_NODE (cur),
        "number of arguments muste be <= number of parameters in 'fun'");
    sprintf (strtrapi + strlen (strtrapi), " %p", args[i]);
    cur = BTOR_REAL_ADDR_NODE (cur->e[1]);
  }
  sprintf (strtrapi + strlen (strtrapi), " %p", fun);
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  btor->external_refs++;
  res = btor_apply_exp (btor, argc, args, fun);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_inc (Btor *btor, BtorNode *exp)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("inc %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);

  btor->external_refs++;
  res = btor_inc_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

BtorNode *
boolector_dec (Btor *btor, BtorNode *exp)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("dec %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);

  btor->external_refs++;
  res = btor_dec_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

int
boolector_get_width (Btor *btor, BtorNode *exp)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("get_width %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  res = btor_get_exp_len (btor, exp);
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_is_array (Btor *btor, BtorNode *exp)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("is_array %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  res = btor_is_array_exp (btor, exp);
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_is_fun (Btor *btor, BtorNode *exp)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("is_fun %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  res = btor_is_lambda_exp (btor, exp);
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_get_fun_arity (Btor *btor, BtorNode *exp)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("get_fun_arity %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  res = btor_get_lambda_arity (btor, exp);
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_get_index_width (Btor *btor, BtorNode *e_array)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("get_index_width %p", e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  e_array = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (e_array);
  res = btor_get_index_exp_len (btor, e_array);
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_fun_sort_check (Btor *btor, int argc, BtorNode **args, BtorNode *fun)
{
  // TODO TRAPI
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (fun);
  BTOR_ABORT_BOOLECTOR (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT_BOOLECTOR (argc >= 1 && !args,
                        "no arguments given but argc defined > 0");
  fun = btor_simplify_exp (btor, fun);
  return btor_fun_sort_check (btor, argc, args, fun);
}

const char *
boolector_get_symbol_of_var (Btor *btor, BtorNode *exp)
{
  const char *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("get_symbol_of_var %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  res = (const char *) btor_get_symbol_exp (btor, exp);
  BTOR_TRAPI_RETURNS (res);
  return res;
}

BtorNode *
boolector_copy (Btor *btor, BtorNode *exp)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("copy %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor->external_refs++;
  res = btor_copy_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

void
boolector_release (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("release %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor->external_refs--;
  btor_release_exp (btor, exp);
}

void
boolector_dump_btor (Btor *btor, FILE *file, BtorNode *exp)
{
  // TODO TRAPI
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor_dump_exp (btor, file, exp);
}

void
boolector_dump_smt (Btor *btor, FILE *file, BtorNode *exp)
{
  // TODO TRAPI
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor_dump_smt1 (btor, file, &exp, 1);
}

void
boolector_dump_smt2 (Btor *btor, FILE *file, BtorNode *exp)
{
  // TODO TRAPI
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor_dump_smt2 (btor, file, &exp, 1);
}

void
boolector_assert (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("assert %p", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (exp)->len != 1,
                        "'exp' must have bit-width one");
  btor_add_constraint_exp (btor, exp);
}

void
boolector_assume (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("assume %p", exp);
  BTOR_ABORT_BOOLECTOR (!btor->inc_enabled,
                        "incremental usage has not been enabled");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (exp)->len != 1,
                        "'exp' must have bit-width one");
  btor_add_assumption_exp (btor, exp);
}

int
boolector_sat (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sat");
  BTOR_ABORT_BOOLECTOR (!btor->inc_enabled && btor->btor_sat_btor_called > 0,
                        "incremental usage has not been enabled."
                        "'boolector_sat' may only be called once");
  res = btor_sat_btor (btor);
  BTOR_TRAPI_RETURN (res);
  return res;
}

char *
boolector_bv_assignment (Btor *btor, BtorNode *exp)
{
  char *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("bv_assignment %p", exp);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_SAT,
      "cannot retrieve assignment if input formula is not SAT");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (!btor->model_gen,
                        "model generation has not been enabled");
  res = btor_bv_assignment_exp (btor, exp);
  BTOR_TRAPI_RETURNP (res);
  return res;
}

void
boolector_free_bv_assignment (Btor *btor, char *assignment)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("free_bv_assignment %p", assignment);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (assignment);
  btor_free_bv_assignment_exp (btor, assignment);
}

void
boolector_array_assignment (
    Btor *btor, BtorNode *e_array, char ***indices, char ***values, int *size)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_SAT,
      "cannot retrieve assignment if input formula is not SAT");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (indices);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (values);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (size);
  BTOR_TRAPI ("array_assignment %p", e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  e_array = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (e_array);
  BTOR_ABORT_BOOLECTOR (!btor->model_gen,
                        "model generation has not been enabled");
  btor_array_assignment_exp (btor, e_array, indices, values, size);
  BTOR_TRAPI ("return %p %p %d", *indices, *values, *size);
}

void
boolector_free_array_assignment (Btor *btor,
                                 char **indices,
                                 char **values,
                                 int size)
{
  int i;

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

  for (i = 0; i < size; i++) btor_free_bv_assignment_exp (btor, indices[i]);
  btor_free (btor->mm, indices, size * sizeof *indices);

  for (i = 0; i < size; i++) btor_free_bv_assignment_exp (btor, values[i]);
  btor_free (btor->mm, values, size * sizeof *values);
}

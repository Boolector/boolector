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

/*------------------------------------------------------------------------*/

Btor *
boolector_new (void)
{
  return btor_new_btor ();
}

Btor *
boolector_clone (Btor *btor)
{
  return btor_clone_btor (btor);
}

int
boolector_is_inconsistent (Btor *btor)
{
  return btor->inconsistent;
}

void
boolector_set_rewrite_level (Btor *btor, int rewrite_level)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "enabling model generation must be done before creating expressions");
  btor_enable_model_gen (btor);
}

void
boolector_generate_model_for_all_reads (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  btor_generate_model_for_all_reads (btor);
}

void
boolector_enable_inc_usage (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "enabling incremental usage must be done before calling 'boolector_sat'");
  btor_enable_inc_usage (btor);
}
int
boolector_set_sat_solver (Btor *btor, const char *solver)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (solver);
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  return btor_set_sat_solver (btor, solver);
}

int
boolector_get_refs (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  return btor->external_refs;
}

void
boolector_delete (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  btor_delete_btor (btor);
}

BtorNode *
boolector_const (Btor *btor, const char *bits)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (bits);
  BTOR_ABORT_BOOLECTOR (*bits == '\0', "'bits' must not be empty");
  btor->external_refs++;
  return btor_const_exp (btor, bits);
}

BtorNode *
boolector_zero (Btor *btor, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_zero_exp (btor, width);
}

BtorNode *
boolector_false (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  btor->external_refs++;
  return btor_false_exp (btor);
}

BtorNode *
boolector_ones (Btor *btor, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_ones_exp (btor, width);
}

BtorNode *
boolector_true (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  btor->external_refs++;
  return btor_true_exp (btor);
}

BtorNode *
boolector_one (Btor *btor, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_one_exp (btor, width);
}

BtorNode *
boolector_unsigned_int (Btor *btor, unsigned int u, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_unsigned_to_exp (btor, u, width);
}

BtorNode *
boolector_int (Btor *btor, int i, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_int_to_exp (btor, i, width);
}

BtorNode *
boolector_var (Btor *btor, int width, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  if (symbol == NULL)
    return btor_var_exp (btor, width, "DVN");
  else
    return btor_var_exp (btor, width, symbol);
}

BtorNode *
boolector_array (Btor *btor,
                 int elem_width,
                 int index_width,
                 const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (elem_width < 1, "'elem_width' must not be < 1");
  BTOR_ABORT_BOOLECTOR (index_width < 1, "'index_width' must not be < 1");
  btor->external_refs++;
  if (symbol == NULL)
    return btor_array_exp (btor, elem_width, index_width, "DAN");
  else
    return btor_array_exp (btor, elem_width, index_width, symbol);
}

BtorNode *
boolector_not (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_not_exp (btor, exp);
}

BtorNode *
boolector_neg (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_neg_exp (btor, exp);
}

BtorNode *
boolector_redor (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_redor_exp (btor, exp);
}

BtorNode *
boolector_redxor (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_redxor_exp (btor, exp);
}

BtorNode *
boolector_redand (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_redand_exp (btor, exp);
}

BtorNode *
boolector_slice (Btor *btor, BtorNode *exp, int upper, int lower)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (lower < 0, "'lower' must not be negative");
  BTOR_ABORT_BOOLECTOR (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT_BOOLECTOR (upper >= BTOR_REAL_ADDR_NODE (exp)->len,
                        "'upper' must not be >= width of 'exp'");
  btor->external_refs++;
  return btor_slice_exp (btor, exp, upper, lower);
}

BtorNode *
boolector_uext (Btor *btor, BtorNode *exp, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  return btor_uext_exp (btor, exp, width);
}

BtorNode *
boolector_sext (Btor *btor, BtorNode *exp, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  return btor_sext_exp (btor, exp, width);
}

BtorNode *
boolector_implies (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_implies_exp (btor, e0, e1);
}

BtorNode *
boolector_iff (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_iff_exp (btor, e0, e1);
}

BtorNode *
boolector_xor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_xor_exp (btor, e0, e1);
}

BtorNode *
boolector_xnor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_xnor_exp (btor, e0, e1);
}

BtorNode *
boolector_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_and_exp (btor, e0, e1);
}

BtorNode *
boolector_nand (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_nand_exp (btor, e0, e1);
}

BtorNode *
boolector_or (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_or_exp (btor, e0, e1);
}

BtorNode *
boolector_nor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_nor_exp (btor, e0, e1);
}

BtorNode *
boolector_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  int is_array_e0, is_array_e1;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_eq_exp (btor, e0, e1);
}

BtorNode *
boolector_ne (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  int is_array_e0, is_array_e1;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_ne_exp (btor, e0, e1);
}

BtorNode *
boolector_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_add_exp (btor, e0, e1);
}

BtorNode *
boolector_uaddo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_uaddo_exp (btor, e0, e1);
}

BtorNode *
boolector_saddo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_saddo_exp (btor, e0, e1);
}

BtorNode *
boolector_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_mul_exp (btor, e0, e1);
}

BtorNode *
boolector_umulo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_umulo_exp (btor, e0, e1);
}

BtorNode *
boolector_smulo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_smulo_exp (btor, e0, e1);
}

BtorNode *
boolector_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_ult_exp (btor, e0, e1);
}

BtorNode *
boolector_slt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_slt_exp (btor, e0, e1);
}

BtorNode *
boolector_ulte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_ulte_exp (btor, e0, e1);
}

BtorNode *
boolector_slte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_slte_exp (btor, e0, e1);
}

BtorNode *
boolector_ugt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_ugt_exp (btor, e0, e1);
}

BtorNode *
boolector_sgt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_sgt_exp (btor, e0, e1);
}

BtorNode *
boolector_ugte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_ugte_exp (btor, e0, e1);
}

BtorNode *
boolector_sgte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_sgte_exp (btor, e0, e1);
}

BtorNode *
boolector_sll (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_sll_exp (btor, e0, e1);
}

BtorNode *
boolector_srl (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_srl_exp (btor, e0, e1);
}

BtorNode *
boolector_sra (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_sra_exp (btor, e0, e1);
}

BtorNode *
boolector_rol (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_rol_exp (btor, e0, e1);
}

BtorNode *
boolector_ror (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_ror_exp (btor, e0, e1);
}

BtorNode *
boolector_sub (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_sub_exp (btor, e0, e1);
}

BtorNode *
boolector_usubo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_usubo_exp (btor, e0, e1);
}

BtorNode *
boolector_ssubo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_ssubo_exp (btor, e0, e1);
}

BtorNode *
boolector_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_udiv_exp (btor, e0, e1);
}

BtorNode *
boolector_sdiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_sdiv_exp (btor, e0, e1);
}

BtorNode *
boolector_sdivo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_sdivo_exp (btor, e0, e1);
}

BtorNode *
boolector_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_urem_exp (btor, e0, e1);
}

BtorNode *
boolector_srem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_srem_exp (btor, e0, e1);
}

BtorNode *
boolector_smod (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_smod_exp (btor, e0, e1);
}

BtorNode *
boolector_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_concat_exp (btor, e0, e1);
}

BtorNode *
boolector_read (Btor *btor, BtorNode *e_array, BtorNode *e_index)
{
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
  return btor_read_exp (btor, e_array, e_index);
}

BtorNode *
boolector_write (Btor *btor,
                 BtorNode *e_array,
                 BtorNode *e_index,
                 BtorNode *e_value)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_write_exp (btor, e_array, e_index, e_value);
}

BtorNode *
boolector_cond (Btor *btor, BtorNode *e_cond, BtorNode *e_if, BtorNode *e_else)
{
  BtorNode *real_e_if, *real_e_else;
  int is_array_e_if, is_array_e_else;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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
  return btor_cond_exp (btor, e_cond, e_if, e_else);
}

BtorNode *
boolector_lambda (Btor *btor, BtorNode *param, BtorNode *exp)
{
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
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");

  btor->external_refs++;
  if (symbol == NULL)
    return btor_param_exp (btor, width, "DPN");
  else
    return btor_param_exp (btor, width, symbol);
}

BtorNode *
boolector_fun (Btor *btor, int paramc, BtorNode **params, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (params);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (paramc < 1, "'paramc' must not be < 1");

  int i;

  for (i = 0; i < paramc; i++)
  {
    BTOR_ABORT_BOOLECTOR (
        !params[i] || !BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (params[i])),
        "'params[%d]' is not a parameter",
        i);
    BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (params[i]);
  }

  btor->external_refs++;
  return btor_fun_exp (btor, paramc, params, exp);
}

// BtorNode *
// boolector_eval (Btor * btor, int argc, BtorNode ** args, BtorNode * lambda)
//{
//  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
//  BTOR_ABORT_ARG_NULL_BOOLECTOR (lambda);
//  BTOR_ABORT_BOOLECTOR (argc < 0, "'argc' must not be < 0");
//  BTOR_ABORT_BOOLECTOR (argc >= 1 && !args,
//                        "no arguments given but argc defined > 0");
//
//  int i;
//  BtorNode *cur = BTOR_REAL_ADDR_NODE (lambda);
//
//  for (i = 0; i < argc; i++)
//    {
//      BTOR_ABORT_BOOLECTOR (!BTOR_IS_LAMBDA_NODE (cur),
//	"number of arguments muste be <= number of parameters in 'lambda'");
//      cur = BTOR_REAL_ADDR_NODE (cur->e[1]);
//    }
//
//  btor->external_refs++;
//  return btor_eval (btor, argc, args, lambda);
//}

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
  int i;
  BtorNode *cur = BTOR_REAL_ADDR_NODE (fun);

  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_BOOLECTOR (
        !BTOR_IS_LAMBDA_NODE (cur),
        "number of arguments muste be <= number of parameters in 'fun'");
    cur = BTOR_REAL_ADDR_NODE (cur->e[1]);
  }

  btor->external_refs++;
  return btor_apply_exp (btor, argc, args, fun);
}

BtorNode *
boolector_inc (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);

  btor->external_refs++;
  return btor_inc_exp (btor, exp);
}

BtorNode *
boolector_dec (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);

  btor->external_refs++;
  return btor_dec_exp (btor, exp);
}

int
boolector_get_width (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  return btor_get_exp_len (btor, exp);
}

int
boolector_is_array (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  return btor_is_array_exp (btor, exp);
}

int
boolector_is_fun (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  return btor_is_lambda_exp (btor, exp);
}

int
boolector_get_fun_arity (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  return btor_get_lambda_arity (btor, exp);
}

int
boolector_get_index_width (Btor *btor, BtorNode *e_array)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  e_array = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (e_array);
  return btor_get_index_exp_len (btor, e_array);
}

int
boolector_fun_sort_check (Btor *btor, int argc, BtorNode **args, BtorNode *fun)
{
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
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  return (const char *) btor_get_symbol_exp (btor, exp);
}

BtorNode *
boolector_copy (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_copy_exp (btor, exp);
}

void
boolector_release (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor->external_refs--;
  btor_release_exp (btor, exp);
}

void
boolector_dump_btor (Btor *btor, FILE *file, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor_dump_exp (btor, file, exp);
}

void
boolector_dump_smt (Btor *btor, FILE *file, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor_dump_smt1 (btor, file, &exp, 1);
}

void
boolector_dump_smt2 (Btor *btor, FILE *file, BtorNode *exp)
{
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
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (!btor->inc_enabled && btor->btor_sat_btor_called > 0,
                        "incremental usage has not been enabled."
                        "'boolector_sat' may only be called once");
  return btor_sat_btor (btor);
}

char *
boolector_bv_assignment (Btor *btor, BtorNode *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (boolector_is_inconsistent (btor));
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (!btor->model_gen,
                        "model generation has not been enabled");
  return btor_bv_assignment_exp (btor, exp);
}

void
boolector_free_bv_assignment (Btor *btor, char *assignment)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (assignment);
  btor_free_bv_assignment_exp (btor, assignment);
}

void
boolector_array_assignment (
    Btor *btor, BtorNode *e_array, char ***indices, char ***values, int *size)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (boolector_is_inconsistent (btor));
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (indices);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (values);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (size);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  e_array = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (e_array);
  BTOR_ABORT_BOOLECTOR (!btor->model_gen,
                        "model generation has not been enabled");
  btor_array_assignment_exp (btor, e_array, indices, values, size);
}

void
boolector_free_array_assignment (Btor *btor,
                                 char **indices,
                                 char **values,
                                 int size)
{
  int i;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
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

  for (i = 0; i < size; i++) boolector_free_bv_assignment (btor, indices[i]);
  btor_free (btor->mm, indices, size * sizeof *indices);

  for (i = 0; i < size; i++) boolector_free_bv_assignment (btor, values[i]);
  btor_free (btor->mm, values, size * sizeof *values);
}

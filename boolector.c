#include "boolector.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btorutil.h"

#include <limits.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/

#define BTOR_ABORT_BOOLECTOR(cond, msg)        \
  do                                           \
  {                                            \
    if (cond)                                  \
    {                                          \
      fputs ("[boolector] " msg "\n", stdout); \
      exit (BTOR_ERR_EXIT);                    \
    }                                          \
  } while (0)

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/

Btor *
boolector_new (void)
{
  return btor_new_btor ();
}

void
boolector_set_rewrite_level (Btor *btor, int rewrite_level)
{
  BTOR_ABORT_BOOLECTOR (
      btor == NULL, "'btor' must not be NULL in 'boolector_set_rewrite_level'");
  BTOR_ABORT_BOOLECTOR (
      rewrite_level < 0 || rewrite_level > 3,
      "'rewrite_level' has to be in [0,3] in 'boolector_set_rewrite_level'");
  BTOR_ABORT_BOOLECTOR (
      btor->id != 1,
      "setting rewrite level must be done before adding expressions");
  btor_set_rewrite_level_btor (btor, rewrite_level);
}

void
boolector_set_verbosity (Btor *btor, int verbosity)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'boolector_set_verbosity'");
  BTOR_ABORT_BOOLECTOR (
      verbosity < -1 || verbosity > 3,
      "'verbosity' has to be in [-1,3] in 'boolector_set_verbosity'");
  BTOR_ABORT_BOOLECTOR (
      btor->id != 1,
      "'setting verbosity must be done before adding expressions'");
  btor_set_verbosity_btor (btor, verbosity);
}

void
boolector_delete (Btor *btor)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'boolector_delete'");
  btor_delete_btor (btor);
}

BtorExp *
boolector_const (Btor *btor, const char *bits)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'boolector_const_exp'");
  BTOR_ABORT_BOOLECTOR (bits == NULL,
                        "'bits' must not be NULL in 'boolector_const_exp'");
  BTOR_ABORT_BOOLECTOR (*bits == '\0',
                        "'bits' must not be empty in 'boolector_const_exp'");
  return btor_const_exp (btor, bits);
}

BtorExp *
boolector_zero (Btor *btor, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_zero_exp'");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1 in 'btor_zero_exp'");
  return btor_zero_exp (btor, len);
}

BtorExp *
boolector_false (Btor *btor)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_false_exp'");
  return btor_false_exp (btor);
}

BtorExp *
boolector_ones (Btor *btor, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_ones_exp'");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1 in 'btor_ones_exp'");
  return btor_ones_exp (btor, len);
}

BtorExp *
boolector_true (Btor *btor)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_true_exp'");
  return btor_true_exp (btor);
}

BtorExp *
boolector_one (Btor *btor, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_one_exp'");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1 in 'btor_one_exp'");
  return btor_one_exp (btor, len);
}

BtorExp *
boolector_unsigned_int (Btor *btor, unsigned int u, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_unsigned_to_exp'");
  BTOR_ABORT_BOOLECTOR (len < 1,
                        "'len' must not be < 1 in 'btor_unsigned_to_exp'");
  return btor_unsigned_to_exp (btor, u, len);
}

BtorExp *
boolector_int (Btor *btor, int i, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_int_to_exp'");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1 in 'btor_int_to_exp'");
  return btor_int_to_exp (btor, i, len);
}

BtorExp *
boolector_var (Btor *btor, int len, const char *symbol)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_var_exp'");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1 in 'btor_var_exp'");
  BTOR_ABORT_BOOLECTOR (symbol == NULL,
                        "'symbol' must not be NULL in 'btor_var_exp'");
  return btor_var_exp (btor, len, symbol);
}

BtorExp *
boolector_array (Btor *btor, int elem_len, int index_len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_array_exp'");
  BTOR_ABORT_BOOLECTOR (elem_len < 1,
                        "'elem_len' must not be < 1 in 'btor_array_exp'");
  BTOR_ABORT_BOOLECTOR (index_len < 1,
                        "'index_len' must not be < 1 in 'btor_array_exp'");
  return btor_array_exp (btor, elem_len, index_len);
}

BtorExp *
boolector_not (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_not_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_not_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array in 'btor_not_exp'");
  return btor_not_exp (btor, exp);
}

BtorExp *
boolector_neg (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_neg_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_neg_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array in 'btor_neg_exp'");
  return btor_neg_exp (btor, exp);
}

BtorExp *
boolector_redor (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_redor_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_redor_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array in 'btor_redor_exp'");
  return btor_redor_exp (btor, exp);
}

BtorExp *
boolector_redxor (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_redxor_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_redxor_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array in 'btor_redxor_exp'");
  return btor_redxor_exp (btor, exp);
}

BtorExp *
boolector_redand (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_redand_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_redand_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array in 'btor_redand_exp'");
  return btor_redand_exp (btor, exp);
}

BtorExp *
boolector_slice (Btor *btor, BtorExp *exp, int upper, int lower)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_slice_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_slice_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array in 'btor_slice_exp'");
  BTOR_ABORT_BOOLECTOR (lower < 0,
                        "'lower' must not be negative in 'btor_slice_exp'");
  BTOR_ABORT_BOOLECTOR (upper < lower,
                        "'upper' must not be < 'lower' in 'btor_slice_exp'");
  BTOR_ABORT_BOOLECTOR (
      upper >= BTOR_REAL_ADDR_EXP (exp)->len,
      "'upper' must not be >= length of 'exp' in 'btor_slice_exp'");
  return btor_slice_exp (btor, exp, upper, lower);
}

BtorExp *
boolector_uext (Btor *btor, BtorExp *exp, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_uext_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_uext_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array in 'btor_uext_exp'");
  BTOR_ABORT_BOOLECTOR (len < 0,
                        "'len' must not be negative in 'btor_uext_exp'");
  return btor_uext_exp (btor, exp, len);
}

BtorExp *
boolector_sext (Btor *btor, BtorExp *exp, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_sext_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_sext_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array in 'btor_sext_exp'");
  BTOR_ABORT_BOOLECTOR (len < 0,
                        "'len' must not be negative in 'btor_sext_exp'");
  return btor_sext_exp (btor, exp, len);
}

BtorExp *
boolector_implies (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_implies_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_implies_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_implies_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_implies_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_implies_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != 1 || BTOR_REAL_ADDR_EXP (e1)->len != 1,
      "length of 'e0' and 'e1' must not be unequal to 1 'btor_implies_exp'");
  return btor_implies_exp (btor, e0, e1);
}

BtorExp *
boolector_iff (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_iff_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_iff_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_iff_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_iff_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_iff_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != 1 || BTOR_REAL_ADDR_EXP (e1)->len != 1,
      "length of 'e0' and 'e1' must not be unequal to 1 in 'btor_iff_exp'");
  return btor_iff_exp (btor, e0, e1);
}

BtorExp *
boolector_xor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_xor_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_xor_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_xor_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_xor_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_xor_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_xor_exp'");
  return btor_xor_exp (btor, e0, e1);
}

BtorExp *
boolector_xnor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_xnor_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_xnor_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_xnor_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_xnor_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_xnor_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_xnor_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return btor_xnor_exp (btor, e0, e1);
}

BtorExp *
boolector_and (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_and_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_and_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_and_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_and_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_and_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_and_exp'");
  return btor_and_exp (btor, e0, e1);
}

BtorExp *
boolector_nand (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_nand_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_nand_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_nand_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_nand_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_nand_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_nand_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return btor_nand_exp (btor, e0, e1);
}

BtorExp *
boolector_or (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_or_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_or_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_or_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_or_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_or_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_or_exp'");
  return btor_or_exp (btor, e0, e1);
}

BtorExp *
boolector_nor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_nor_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_nor_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_nor_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_nor_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_nor_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_nor_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return btor_nor_exp (btor, e0, e1);
}

BtorExp *
boolector_eq (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;

  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_eq_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_eq_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_eq_exp'");
  e0          = btor_pointer_chase_simplified_exp (btor, e0);
  e1          = btor_pointer_chase_simplified_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  BTOR_ABORT_BOOLECTOR (
      is_array_e0 != is_array_e1,
      "array must not be compared with bit vector in 'btor_eq_exp'");
  BTOR_ABORT_BOOLECTOR (
      !is_array_e0 && real_e0->len != real_e1->len,
      "bit vectors must not have unequal length in 'btor_eq_exp'");
  BTOR_ABORT_BOOLECTOR (
      is_array_e0 && real_e0->len != real_e1->len,
      "arrays must not have unequal element length in 'btor_eq_exp'");
  BTOR_ABORT_BOOLECTOR (
      is_array_e0 && real_e0->index_len != real_e1->index_len,
      "arrays must not have unequal index length in 'btor_eq_exp'");
  return btor_eq_exp (btor, e0, e1);
}

BtorExp *
boolector_ne (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_ne_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_ne_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_ne_exp'");
  e0          = btor_pointer_chase_simplified_exp (btor, e0);
  e1          = btor_pointer_chase_simplified_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  BTOR_ABORT_BOOLECTOR (
      is_array_e0 != is_array_e1,
      "array must not be compared with bit vector in 'btor_ne_exp'");
  BTOR_ABORT_BOOLECTOR (
      is_array_e0 && real_e0->len != real_e1->len,
      "arrays must not have unequal element length in 'btor_ne_exp'");
  BTOR_ABORT_BOOLECTOR (
      is_array_e0 && real_e0->index_len != real_e1->index_len,
      "arrays must not have unequal index length in 'btor_ne_exp'");
  assert (!is_array_e0 || real_e0->index_len > 0);
  assert (!is_array_e0
          || (BTOR_IS_REGULAR_EXP (e0) && BTOR_IS_REGULAR_EXP (e1)));
  assert (real_e0->len > 0);
  return btor_ne_exp (btor, e0, e1);
}

BtorExp *
boolector_add (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_add_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_add_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_add_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_add_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_add_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_add_exp'");
  return btor_add_exp (btor, e0, e1);
}

BtorExp *
boolector_uaddo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_uaddo_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_uaddo_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_uaddo_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_uaddo_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_uaddo_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_uaddo_exp'");
  return btor_uaddo_exp (btor, e0, e1);
}

BtorExp *
boolector_saddo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_saddo_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_saddo_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_saddo_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_saddo_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_saddo_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_saddo_exp'");
  return btor_saddo_exp (btor, e0, e1);
}

BtorExp *
boolector_mul (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_mul_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_mul_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_mul_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_mul_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_mul_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_mul_exp'");
  return btor_mul_exp (btor, e0, e1);
}

BtorExp *
boolector_umulo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_umulo_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_umulo_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_umulo_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_umulo_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_umulo_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_umulo_exp'");
  return btor_umulo_exp (btor, e0, e1);
}

BtorExp *
boolector_smulo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_smulo_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_smulo_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_smulo_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_smulo_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_smulo_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_smulo_exp'");
  return btor_smulo_exp (btor, e0, e1);
}

BtorExp *
boolector_ult (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_ult_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_ult_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_ult_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_ult_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_ult_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ult_exp'");
  return btor_ult_exp (btor, e0, e1);
}

BtorExp *
boolector_slt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_slt_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_slt_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_slt_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_slt_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_slt_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_slt_exp'");
  return btor_slt_exp (btor, e0, e1);
}

BtorExp *
boolector_ulte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_ulte_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_ulte_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_ulte_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_ulte_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_ulte_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ulte_exp'");
  return btor_ulte_exp (btor, e0, e1);
}

BtorExp *
boolector_slte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_slte_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_slte_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_slte_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_slte_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_slte_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_slte_exp'");
  return btor_slte_exp (btor, e0, e1);
}

BtorExp *
boolector_ugt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_ugt_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_ugt_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_ugt_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_ugt_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_ugt_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ugt_exp'");
  return btor_ugt_exp (btor, e0, e1);
}

BtorExp *
boolector_sgt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_sgt_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_sgt_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_sgt_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_sgt_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_sgt_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sgt_exp'");
  return btor_sgt_exp (btor, e0, e1);
}

BtorExp *
boolector_ugte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_ugte_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_ugte_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_ugte_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_ugte_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_ugte_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ugte_exp'");
  return btor_ugte_exp (btor, e0, e1);
}

BtorExp *
boolector_sgte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_sgte_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_sgte_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_sgte_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_sgte_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_sgte_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sgte_exp'");
  return btor_sgte_exp (btor, e0, e1);
}

BtorExp *
boolector_sll (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_sll_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_sll_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_sll_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_sll_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_sll_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (
      !btor_is_power_of_2_util (len),
      "length of 'e0' must be a power of 2 in 'btor_sll_exp'");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_sll_exp'");
  return btor_sll_exp (btor, e0, e1);
}

BtorExp *
boolector_srl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_srl_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_srl_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_srl_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_srl_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_srl_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (
      !btor_is_power_of_2_util (len),
      "length of 'e0' must be a power of 2 in 'btor_srl_exp'");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_srl_exp'");
  return btor_srl_exp (btor, e0, e1);
}

BtorExp *
boolector_sra (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_sra_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_sra_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_sra_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_sra_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_sra_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (
      !btor_is_power_of_2_util (len),
      "length of 'e0' must be a power of 2 in 'btor_sra_exp'");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_sra_exp'");
  return btor_sra_exp (btor, e0, e1);
}

BtorExp *
boolector_rol (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_rol_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_rol_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_rol_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_rol_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_rol_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (
      !btor_is_power_of_2_util (len),
      "length of 'e0' must be a power of 2 in 'btor_rol_exp'");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_rol_exp'");
  return btor_rol_exp (btor, e0, e1);
}

BtorExp *
boolector_ror (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_ror_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_ror_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_ror_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_ror_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_ror_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (
      !btor_is_power_of_2_util (len),
      "length of 'e0' must be a power of 2 in 'btor_ror_exp'");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_ror_exp'");
  return btor_ror_exp (btor, e0, e1);
}

BtorExp *
boolector_sub (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_sub_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_sub_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_sub_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_sub_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_sub_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sub_exp'");
  return btor_sub_exp (btor, e0, e1);
}

BtorExp *
boolector_usubo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_usubo_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_usubo_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_usubo_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_usubo_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_usubo_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_usubo_exp'");
  return btor_usubo_exp (btor, e0, e1);
}

BtorExp *
boolector_ssubo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_ssubo_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_ssubo_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_ssubo_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_ssubo_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_ssubo_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ssubo_exp'");
  return btor_ssubo_exp (btor, e0, e1);
}

BtorExp *
boolector_udiv (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_udiv_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_udiv_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_udiv_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_udiv_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_udiv_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_udiv_exp'");
  return btor_udiv_exp (btor, e0, e1);
}

BtorExp *
boolector_sdiv (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_sdiv_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_sdiv_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_sdiv_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_sdiv_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_sdiv_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sdiv_exp'");
  return btor_sdiv_exp (btor, e0, e1);
}

BtorExp *
boolector_sdivo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_sdivo_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_sdivo_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_sdivo_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_sdivo_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_sdivo_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sdivo_exp'");
  return btor_sdivo_exp (btor, e0, e1);
}

BtorExp *
boolector_urem (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_urem_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_urem_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_urem_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_urem_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_urem_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_urem_exp'");
  return btor_urem_exp (btor, e0, e1);
}

BtorExp *
boolector_srem (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_srem_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_srem_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_srem_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_srem_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_srem_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_srem_exp'");
  return btor_srem_exp (btor, e0, e1);
}

BtorExp *
boolector_smod (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_smod_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL in 'btor_smod_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL in 'btor_smod_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_smod_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_smod_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_smod_exp'");
  return btor_smod_exp (btor, e0, e1);
}

BtorExp *
boolector_concat (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_concat_exp'");
  BTOR_ABORT_BOOLECTOR (e0 == NULL,
                        "'e0' must not be NULL in 'btor_concat_exp'");
  BTOR_ABORT_BOOLECTOR (e1 == NULL,
                        "'e1' must not be NULL in 'btor_concat_exp'");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array in 'btor_concat_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array in 'btor_concat_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len > INT_MAX - BTOR_REAL_ADDR_EXP (e1)->len,
      "length of result is too large in 'btor_concat_exp'");
  return btor_concat_exp (btor, e0, e1);
}

BtorExp *
boolector_read (Btor *btor, BtorExp *e_array, BtorExp *e_index)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_read_exp'");
  BTOR_ABORT_BOOLECTOR (e_array == NULL,
                        "'e_array' must not be NULL in 'btor_read_exp'");
  BTOR_ABORT_BOOLECTOR (e_index == NULL,
                        "'e_index' must not be NULL in 'btor_read_exp'");
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  BTOR_ABORT_BOOLECTOR (
      !BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
      "'e_array' must not be a bit vector in 'btor_read_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)),
                        "'e_index' must not be an array in 'btor_read_exp'");
  BTOR_ABORT_BOOLECTOR (e_array->index_len != BTOR_REAL_ADDR_EXP (e_index)->len,
                        "index length of 'e_array' and length of 'e_index' "
                        "must not be unequal in 'btor_read_exp'");
  return btor_read_exp (btor, e_array, e_index);
}

BtorExp *
boolector_write (Btor *btor,
                 BtorExp *e_array,
                 BtorExp *e_index,
                 BtorExp *e_value)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_write_exp'");
  BTOR_ABORT_BOOLECTOR (e_array == NULL,
                        "'e_array' must not be NULL in 'btor_write_exp'");
  BTOR_ABORT_BOOLECTOR (e_index == NULL,
                        "'e_index' must not be NULL in 'btor_write_exp'");
  BTOR_ABORT_BOOLECTOR (e_value == NULL,
                        "'e_value' must not be NULL in 'btor_write_exp'");
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  e_value = btor_pointer_chase_simplified_exp (btor, e_value);
  BTOR_ABORT_BOOLECTOR (
      !BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
      "'e_array' must not be a bit vector in 'btor_write_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)),
                        "'e_index' must not be an array in 'btor_write_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)),
      "'e_value' must not be a bit vector in 'btor_write_exp'");
  BTOR_ABORT_BOOLECTOR (e_array->index_len != BTOR_REAL_ADDR_EXP (e_index)->len,
                        "index length of 'e_array' and length of 'e_index' "
                        "must not be unequal in 'btor_write_exp'");
  BTOR_ABORT_BOOLECTOR (e_array->len != BTOR_REAL_ADDR_EXP (e_value)->len,
                        "element length of 'e_array' and length of 'e_value' "
                        "must not be unequal in 'btor_write_exp'");
  return btor_write_exp (btor, e_array, e_index, e_value);
}

BtorExp *
boolector_cond (Btor *btor, BtorExp *e_cond, BtorExp *e_if, BtorExp *e_else)
{
  BtorExp *real_e_if, *real_e_else;
  int is_array_e_if, is_array_e_else;

  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_cond_exp'");
  BTOR_ABORT_BOOLECTOR (e_cond == NULL,
                        "'e_cond' must not be NULL in 'btor_cond_exp'");
  BTOR_ABORT_BOOLECTOR (e_if == NULL,
                        "'e_if' must not be NULL in 'btor_cond_exp'");
  BTOR_ABORT_BOOLECTOR (e_else == NULL,
                        "'e_else' must not be NULL in 'btor_cond_exp'");
  e_cond = btor_pointer_chase_simplified_exp (btor, e_cond);
  e_if   = btor_pointer_chase_simplified_exp (btor, e_if);
  e_else = btor_pointer_chase_simplified_exp (btor, e_else);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)),
                        "'e_cond' must not be an array in 'btor_cond_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e_cond)->len != 1,
      "length of 'e_cond' must be equal to 1 in 'btor_cond_exp'");
  real_e_if       = BTOR_REAL_ADDR_EXP (e_if);
  real_e_else     = BTOR_REAL_ADDR_EXP (e_else);
  is_array_e_if   = BTOR_IS_ARRAY_EXP (real_e_if);
  is_array_e_else = BTOR_IS_ARRAY_EXP (real_e_else);
  BTOR_ABORT_BOOLECTOR (
      is_array_e_if != is_array_e_else,
      "array must not be combined with bit vector in 'btor_cond_exp'");
  BTOR_ABORT_BOOLECTOR (
      !is_array_e_if && real_e_if->len != real_e_else->len,
      "bit vectors must not have unequal length in 'btor_cond_exp'");
  BTOR_ABORT_BOOLECTOR (
      is_array_e_if && real_e_if->len != real_e_else->len,
      "arrays must not have unequal element length in 'btor_cond_exp'");
  BTOR_ABORT_BOOLECTOR (
      is_array_e_if && real_e_if->index_len != real_e_else->index_len,
      "arrays must not have unequal index length in 'btor_cond_exp'");
  return btor_cond_exp (btor, e_cond, e_if, e_else);
}

BtorExp *
boolector_inc (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_inc_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_inc_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'e0' must not be an array in 'btor_inc_exp'");
  return btor_inc_exp (btor, exp);
}

BtorExp *
boolector_dec (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_dec_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_dec_exp'");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'e0' must not be an array in 'btor_dec_exp'");
  return btor_dec_exp (btor, exp);
}

int
boolector_get_bw (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_get_exp_len'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_get_exp_len'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return btor_get_exp_len (btor, exp);
}

int
boolector_is_array (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_is_array_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_is_array_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return btor_is_array_exp (btor, exp);
}

int
boolector_get_bw_of_index (Btor *btor, BtorExp *e_array)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_get_index_exp_len'");
  BTOR_ABORT_BOOLECTOR (
      e_array == NULL,
      "'e_array' must not be NULL in 'btor_get_index_exp_len'");
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  BTOR_ABORT_BOOLECTOR (
      !BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
      "'e_array' must not be a bit-vector in 'btor_get_index_exp_len'");
  return btor_get_index_exp_len (btor, e_array);
}

char *
boolector_get_symbol_of_var (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_get_symbol_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_get_symbol_exp'");
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' has to be a variable in 'btor_get_symbol_exp'");
  return btor_get_symbol_exp (btor, exp);
}

BtorExp *
boolector_copy (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_copy_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_copy_exp'");
  return btor_copy_exp (btor, exp);
}

void
boolector_release (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_release_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_release_exp'");
  btor_release_exp (btor, exp);
}

void
boolector_dump_btor (Btor *btor, FILE *file, BtorExp *root)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_dump_exp'");
  BTOR_ABORT_BOOLECTOR (file == NULL,
                        "'file' must not be NULL in 'btor_dump_exp'");
  BTOR_ABORT_BOOLECTOR (root == NULL,
                        "'root' must not be NULL in 'btor_dump_exp'");
  btor_dump_exp (btor, file, root);
}

void
boolector_dump_smt (Btor *btor, FILE *file, BtorExp *root)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_smt_exp'");
  BTOR_ABORT_BOOLECTOR (file == NULL,
                        "'file' must not be NULL in 'btor_smt_exp'");
  BTOR_ABORT_BOOLECTOR (root == NULL,
                        "'root' must not be NULL in 'btor_smt_exp'");
  btor_dump_smt (btor, file, root);
}

void
boolector_add_constraint (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_add_constraint_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_add_constraint_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (
      BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
      "'exp' must not be an array in 'btor_add_constraint_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (exp)->len != 1,
      "'exp' has to be a boolean expression in 'btor_add_constraint_exp'");
  btor_add_constraint_exp (btor, exp);
}

void
boolector_add_assumption (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'btor_add_assumption_exp'");
  BTOR_ABORT_BOOLECTOR (exp == NULL,
                        "'exp' must not be NULL in 'btor_add_assumption_exp'");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (
      BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
      "'exp' must not be an array in 'btor_add_assumption_exp'");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (exp)->len != 1,
      "'exp' has to be a boolean expression in 'btor_add_assumption_exp'");
  btor_add_assumption_exp (btor, exp);
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/

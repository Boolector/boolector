#include "boolector.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btorutil.h"

#include <limits.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/

#define BTOR_ABORT_BOOLECTOR(cond, msg)               \
  do                                                  \
  {                                                   \
    if (cond)                                         \
    {                                                 \
      printf ("[boolector] %s: %s\n", __func__, msg); \
      fflush (stdout);                                \
      exit (BTOR_ERR_EXIT);                           \
    }                                                 \
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
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (rewrite_level < 0 || rewrite_level > 3,
                        "'rewrite_level' has to be in [0,3]");
  BTOR_ABORT_BOOLECTOR (
      btor->id != 1,
      "setting rewrite level must be done before adding expressions");
  btor_set_rewrite_level_btor (btor, rewrite_level);
}

void
boolector_set_verbosity (Btor *btor, int verbosity)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (verbosity < -1 || verbosity > 3,
                        "'verbosity' has to be in [-1,3]");
  BTOR_ABORT_BOOLECTOR (
      btor->id != 1,
      "'setting verbosity must be done before adding expressions'");
  btor_set_verbosity_btor (btor, verbosity);
}

void
boolector_delete (Btor *btor)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  btor_delete_btor (btor);
}

BtorExp *
boolector_const (Btor *btor, const char *bits)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (bits == NULL, "'bits' must not be NULL");
  BTOR_ABORT_BOOLECTOR (*bits == '\0', "'bits' must not be empty");
  return btor_const_exp (btor, bits);
}

BtorExp *
boolector_zero (Btor *btor, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1");
  return btor_zero_exp (btor, len);
}

BtorExp *
boolector_false (Btor *btor)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  return btor_false_exp (btor);
}

BtorExp *
boolector_ones (Btor *btor, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1");
  return btor_ones_exp (btor, len);
}

BtorExp *
boolector_true (Btor *btor)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  return btor_true_exp (btor);
}

BtorExp *
boolector_one (Btor *btor, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1");
  return btor_one_exp (btor, len);
}

BtorExp *
boolector_unsigned_int (Btor *btor, unsigned int u, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1");
  return btor_unsigned_to_exp (btor, u, len);
}

BtorExp *
boolector_int (Btor *btor, int i, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1");
  return btor_int_to_exp (btor, i, len);
}

BtorExp *
boolector_var (Btor *btor, int len, const char *symbol)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (len < 1, "'len' must not be < 1");
  BTOR_ABORT_BOOLECTOR (symbol == NULL, "'symbol' must not be NULL");
  return btor_var_exp (btor, len, symbol);
}

BtorExp *
boolector_array (Btor *btor, int elem_len, int index_len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (elem_len < 1, "'elem_len' must not be < 1");
  BTOR_ABORT_BOOLECTOR (index_len < 1, "'index_len' must not be < 1");
  return btor_array_exp (btor, elem_len, index_len);
}

BtorExp *
boolector_not (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  return btor_not_exp (btor, exp);
}

BtorExp *
boolector_neg (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  return btor_neg_exp (btor, exp);
}

BtorExp *
boolector_redor (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  return btor_redor_exp (btor, exp);
}

BtorExp *
boolector_redxor (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  return btor_redxor_exp (btor, exp);
}

BtorExp *
boolector_redand (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  return btor_redand_exp (btor, exp);
}

BtorExp *
boolector_slice (Btor *btor, BtorExp *exp, int upper, int lower)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  BTOR_ABORT_BOOLECTOR (lower < 0, "'lower' must not be negative");
  BTOR_ABORT_BOOLECTOR (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT_BOOLECTOR (upper >= BTOR_REAL_ADDR_EXP (exp)->len,
                        "'upper' must not be >= length of 'exp'");
  return btor_slice_exp (btor, exp, upper, lower);
}

BtorExp *
boolector_uext (Btor *btor, BtorExp *exp, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  BTOR_ABORT_BOOLECTOR (len < 0, "'len' must not be negative");
  return btor_uext_exp (btor, exp, len);
}

BtorExp *
boolector_sext (Btor *btor, BtorExp *exp, int len)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  BTOR_ABORT_BOOLECTOR (len < 0, "'len' must not be negative");
  return btor_sext_exp (btor, exp, len);
}

BtorExp *
boolector_implies (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != 1 || BTOR_REAL_ADDR_EXP (e1)->len != 1,
      "length of 'e0' and 'e1' must not be unequal to 1");
  return btor_implies_exp (btor, e0, e1);
}

BtorExp *
boolector_iff (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != 1 || BTOR_REAL_ADDR_EXP (e1)->len != 1,
      "length of 'e0' and 'e1' must not be unequal to 1");
  return btor_iff_exp (btor, e0, e1);
}

BtorExp *
boolector_xor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_xor_exp (btor, e0, e1);
}

BtorExp *
boolector_xnor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_xnor_exp (btor, e0, e1);
}

BtorExp *
boolector_and (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_and_exp (btor, e0, e1);
}

BtorExp *
boolector_nand (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_nand_exp (btor, e0, e1);
}

BtorExp *
boolector_or (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_or_exp (btor, e0, e1);
}

BtorExp *
boolector_nor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_nor_exp (btor, e0, e1);
}

BtorExp *
boolector_eq (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;

  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0          = btor_pointer_chase_simplified_exp (btor, e0);
  e1          = btor_pointer_chase_simplified_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  BTOR_ABORT_BOOLECTOR (is_array_e0 != is_array_e1,
                        "array must not be compared with bit vector");
  BTOR_ABORT_BOOLECTOR (!is_array_e0 && real_e0->len != real_e1->len,
                        "bit vectors must not have unequal length");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->len != real_e1->len,
                        "arrays must not have unequal element length");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->index_len != real_e1->index_len,
                        "arrays must not have unequal index length");
  return btor_eq_exp (btor, e0, e1);
}

BtorExp *
boolector_ne (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0          = btor_pointer_chase_simplified_exp (btor, e0);
  e1          = btor_pointer_chase_simplified_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  BTOR_ABORT_BOOLECTOR (is_array_e0 != is_array_e1,
                        "array must not be compared with bit vector");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->len != real_e1->len,
                        "arrays must not have unequal element length");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->index_len != real_e1->index_len,
                        "arrays must not have unequal index length");
  return btor_ne_exp (btor, e0, e1);
}

BtorExp *
boolector_add (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_add_exp (btor, e0, e1);
}

BtorExp *
boolector_uaddo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_uaddo_exp (btor, e0, e1);
}

BtorExp *
boolector_saddo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_saddo_exp (btor, e0, e1);
}

BtorExp *
boolector_mul (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_mul_exp (btor, e0, e1);
}

BtorExp *
boolector_umulo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_umulo_exp (btor, e0, e1);
}

BtorExp *
boolector_smulo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_smulo_exp (btor, e0, e1);
}

BtorExp *
boolector_ult (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_ult_exp (btor, e0, e1);
}

BtorExp *
boolector_slt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_slt_exp (btor, e0, e1);
}

BtorExp *
boolector_ulte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_ulte_exp (btor, e0, e1);
}

BtorExp *
boolector_slte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_slte_exp (btor, e0, e1);
}

BtorExp *
boolector_ugt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_ugt_exp (btor, e0, e1);
}

BtorExp *
boolector_sgt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_sgt_exp (btor, e0, e1);
}

BtorExp *
boolector_ugte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_ugte_exp (btor, e0, e1);
}

BtorExp *
boolector_sgte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_sgte_exp (btor, e0, e1);
}

BtorExp *
boolector_sll (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "length of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
                        "length of 'e1' must be equal to log2(length of 'e0')");
  return btor_sll_exp (btor, e0, e1);
}

BtorExp *
boolector_srl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "length of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
                        "length of 'e1' must be equal to log2(length of 'e0')");
  return btor_srl_exp (btor, e0, e1);
}

BtorExp *
boolector_sra (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "length of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
                        "length of 'e1' must be equal to log2(length of 'e0')");
  return btor_sra_exp (btor, e0, e1);
}

BtorExp *
boolector_rol (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "length of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
                        "length of 'e1' must be equal to log2(length of 'e0')");
  return btor_rol_exp (btor, e0, e1);
}

BtorExp *
boolector_ror (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "length of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
                        "length of 'e1' must be equal to log2(length of 'e0')");
  return btor_ror_exp (btor, e0, e1);
}

BtorExp *
boolector_sub (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_sub_exp (btor, e0, e1);
}

BtorExp *
boolector_usubo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_usubo_exp (btor, e0, e1);
}

BtorExp *
boolector_ssubo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_ssubo_exp (btor, e0, e1);
}

BtorExp *
boolector_udiv (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_udiv_exp (btor, e0, e1);
}

BtorExp *
boolector_sdiv (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_sdiv_exp (btor, e0, e1);
}

BtorExp *
boolector_sdivo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_sdivo_exp (btor, e0, e1);
}

BtorExp *
boolector_urem (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_urem_exp (btor, e0, e1);
}

BtorExp *
boolector_srem (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_srem_exp (btor, e0, e1);
}

BtorExp *
boolector_smod (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal");
  return btor_smod_exp (btor, e0, e1);
}

BtorExp *
boolector_concat (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e0 == NULL, "'e0' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e1 == NULL, "'e1' must not be NULL");
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                        "'e0' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                        "'e1' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len > INT_MAX - BTOR_REAL_ADDR_EXP (e1)->len,
      "length of result is too large");
  return btor_concat_exp (btor, e0, e1);
}

BtorExp *
boolector_read (Btor *btor, BtorExp *e_array, BtorExp *e_index)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_array == NULL, "'e_array' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_index == NULL, "'e_index' must not be NULL");
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
                        "'e_array' must not be a bit vector");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)),
                        "'e_index' must not be an array");
  BTOR_ABORT_BOOLECTOR (
      e_array->index_len != BTOR_REAL_ADDR_EXP (e_index)->len,
      "index length of 'e_array' and length of 'e_index' must not be unequal");
  return btor_read_exp (btor, e_array, e_index);
}

BtorExp *
boolector_write (Btor *btor,
                 BtorExp *e_array,
                 BtorExp *e_index,
                 BtorExp *e_value)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_array == NULL, "'e_array' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_index == NULL, "'e_index' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_value == NULL, "'e_value' must not be NULL");
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  e_value = btor_pointer_chase_simplified_exp (btor, e_value);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
                        "'e_array' must not be a bit vector");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)),
                        "'e_index' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)),
                        "'e_value' must not be a bit vector");
  BTOR_ABORT_BOOLECTOR (
      e_array->index_len != BTOR_REAL_ADDR_EXP (e_index)->len,
      "index length of 'e_array' and length of 'e_index' must not be unequal");
  BTOR_ABORT_BOOLECTOR (e_array->len != BTOR_REAL_ADDR_EXP (e_value)->len,
                        "element length of 'e_array' and length of 'e_value' "
                        "must not be unequal");
  return btor_write_exp (btor, e_array, e_index, e_value);
}

BtorExp *
boolector_cond (Btor *btor, BtorExp *e_cond, BtorExp *e_if, BtorExp *e_else)
{
  BtorExp *real_e_if, *real_e_else;
  int is_array_e_if, is_array_e_else;

  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_cond == NULL, "'e_cond' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_if == NULL, "'e_if' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_else == NULL, "'e_else' must not be NULL");
  e_cond = btor_pointer_chase_simplified_exp (btor, e_cond);
  e_if   = btor_pointer_chase_simplified_exp (btor, e_if);
  e_else = btor_pointer_chase_simplified_exp (btor, e_else);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)),
                        "'e_cond' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_EXP (e_cond)->len != 1,
                        "length of 'e_cond' must be equal to 1");
  real_e_if       = BTOR_REAL_ADDR_EXP (e_if);
  real_e_else     = BTOR_REAL_ADDR_EXP (e_else);
  is_array_e_if   = BTOR_IS_ARRAY_EXP (real_e_if);
  is_array_e_else = BTOR_IS_ARRAY_EXP (real_e_else);
  BTOR_ABORT_BOOLECTOR (is_array_e_if != is_array_e_else,
                        "array must not be combined with bit vector");
  BTOR_ABORT_BOOLECTOR (!is_array_e_if && real_e_if->len != real_e_else->len,
                        "bit vectors must not have unequal length");
  BTOR_ABORT_BOOLECTOR (is_array_e_if && real_e_if->len != real_e_else->len,
                        "arrays must not have unequal element length");
  BTOR_ABORT_BOOLECTOR (
      is_array_e_if && real_e_if->index_len != real_e_else->index_len,
      "arrays must not have unequal index length");
  return btor_cond_exp (btor, e_cond, e_if, e_else);
}

BtorExp *
boolector_inc (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'e0' must not be an array");
  return btor_inc_exp (btor, exp);
}

BtorExp *
boolector_dec (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'e0' must not be an array");
  return btor_dec_exp (btor, exp);
}

int
boolector_get_len (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return btor_get_exp_len (btor, exp);
}

int
boolector_is_array (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return btor_is_array_exp (btor, exp);
}

int
boolector_get_index_len (Btor *btor, BtorExp *e_array)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (e_array == NULL, "'e_array' must not be NULL");
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
                        "'e_array' must not be a bit-vector");
  return btor_get_index_exp_len (btor, e_array);
}

char *
boolector_get_symbol_of_var (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' has to be a variable");
  return btor_get_symbol_exp (btor, exp);
}

BtorExp *
boolector_copy (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  return btor_copy_exp (btor, exp);
}

void
boolector_release (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  btor_release_exp (btor, exp);
}

void
boolector_dump_btor (Btor *btor, FILE *file, BtorExp *root)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (file == NULL, "'file' must not be NULL");
  BTOR_ABORT_BOOLECTOR (root == NULL, "'root' must not be NULL");
  btor_dump_exp (btor, file, root);
}

void
boolector_dump_smt (Btor *btor, FILE *file, BtorExp *root)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (file == NULL, "'file' must not be NULL");
  BTOR_ABORT_BOOLECTOR (root == NULL, "'root' must not be NULL");
  btor_dump_smt (btor, file, root);
}

void
boolector_add_constraint (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_EXP (exp)->len != 1,
                        "'exp' has to be a boolean expression");
  btor_add_constraint_exp (btor, exp);
}

void
boolector_add_assumption (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_EXP (exp)->len != 1,
                        "'exp' has to be a boolean expression");
  btor_add_assumption_exp (btor, exp);
}

int
boolector_sat (Btor *btor, int refinement_limit)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (refinement_limit < 0,
                        "'refinement_limit' must not be negative");
  return btor_sat_btor (btor, refinement_limit);
}

const char *
boolector_assignment (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL, "'btor' must not be NULL");
  BTOR_ABORT_BOOLECTOR (exp == NULL, "'exp' must not be NULL");
  BTOR_ABORT_BOOLECTOR (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                        "'exp' must not be an array");
  return btor_assignment_exp (btor, exp);
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/

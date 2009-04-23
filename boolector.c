#include "boolector.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btorutil.h"

#include <limits.h>
#include <stdio.h>

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

#define BTOR_ABORT_ARG_NULL_BOOLECTOR(arg)      \
  do                                            \
  {                                             \
    if ((arg) == NULL)                          \
    {                                           \
      printf ("[boolector] %s: ", __func__);    \
      printf ("'%s' must not be NULL\n", #arg); \
      fflush (stdout);                          \
      exit (BTOR_ERR_EXIT);                     \
    }                                           \
  } while (0)

#define BTOR_ABORT_REFS_NOT_POS_BOOLECTOR(arg)                      \
  do                                                                \
  {                                                                 \
    if (BTOR_REAL_ADDR_EXP ((arg))->refs < 1)                       \
    {                                                               \
      printf ("[boolector] %s: ", __func__);                        \
      printf ("reference counter of '%s' must not be < 1\n", #arg); \
      fflush (stdout);                                              \
      exit (BTOR_ERR_EXIT);                                         \
    }                                                               \
  } while (0)

#define BTOR_ABORT_ARRAY_BOOLECTOR(arg)                 \
  do                                                    \
  {                                                     \
    if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP ((arg)))) \
    {                                                   \
      printf ("[boolector] %s: ", __func__);            \
      printf ("'%s' must not be an array\n", #arg);     \
      fflush (stdout);                                  \
      exit (BTOR_ERR_EXIT);                             \
    }                                                   \
  } while (0)

#define BTOR_ABORT_BV_BOLECTOR(arg)                      \
  do                                                     \
  {                                                      \
    if (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP ((arg)))) \
    {                                                    \
      printf ("[boolector] %s: ", __func__);             \
      printf ("'%s' must not be a bit-vector\n", #arg);  \
      fflush (stdout);                                   \
      exit (BTOR_ERR_EXIT);                              \
    }                                                    \
  } while (0)

#define BTOR_ABORT_NE_BW(arg1, arg2)                                          \
  do                                                                          \
  {                                                                           \
    if (BTOR_REAL_ADDR_EXP ((arg1))->len != BTOR_REAL_ADDR_EXP ((arg2))->len) \
    {                                                                         \
      printf ("[boolector] %s: ", __func__);                                  \
      printf (                                                                \
          "bit-width of '%s' and '%s' must not be unequal\n", #arg1, #arg2);  \
      exit (BTOR_ERR_EXIT);                                                   \
    }                                                                         \
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
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (rewrite_level < 0 || rewrite_level > 3,
                        "'rewrite_level' has to be in [0,3]");
  BTOR_ABORT_BOOLECTOR (
      btor->id != 1,
      "setting rewrite level must be done before creating expressions");
  btor_set_rewrite_level_btor (btor, rewrite_level);
}

void
boolector_enable_model_gen (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->id != 1,
      "enabling model generation must be done before creating expressions");
  btor_enable_model_gen (btor);
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

BtorExp *
boolector_const (Btor *btor, const char *bits)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (bits);
  BTOR_ABORT_BOOLECTOR (*bits == '\0', "'bits' must not be empty");
  btor->external_refs++;
  return btor_const_exp (btor, bits);
}

BtorExp *
boolector_zero (Btor *btor, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_zero_exp (btor, width);
}

BtorExp *
boolector_false (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  btor->external_refs++;
  return btor_false_exp (btor);
}

BtorExp *
boolector_ones (Btor *btor, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_ones_exp (btor, width);
}

BtorExp *
boolector_true (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  btor->external_refs++;
  return btor_true_exp (btor);
}

BtorExp *
boolector_one (Btor *btor, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_one_exp (btor, width);
}

BtorExp *
boolector_unsigned_int (Btor *btor, unsigned int u, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_unsigned_to_exp (btor, u, width);
}

BtorExp *
boolector_int (Btor *btor, int i, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  return btor_int_to_exp (btor, i, width);
}

BtorExp *
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

BtorExp *
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

BtorExp *
boolector_not (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_not_exp (btor, exp);
}

BtorExp *
boolector_neg (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_neg_exp (btor, exp);
}

BtorExp *
boolector_redor (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_redor_exp (btor, exp);
}

BtorExp *
boolector_redxor (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_redxor_exp (btor, exp);
}

BtorExp *
boolector_redand (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_redand_exp (btor, exp);
}

BtorExp *
boolector_slice (Btor *btor, BtorExp *exp, int upper, int lower)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (lower < 0, "'lower' must not be negative");
  BTOR_ABORT_BOOLECTOR (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT_BOOLECTOR (upper >= BTOR_REAL_ADDR_EXP (exp)->len,
                        "'upper' must not be >= width of 'exp'");
  btor->external_refs++;
  return btor_slice_exp (btor, exp, upper, lower);
}

BtorExp *
boolector_uext (Btor *btor, BtorExp *exp, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  return btor_uext_exp (btor, exp, width);
}

BtorExp *
boolector_sext (Btor *btor, BtorExp *exp, int width)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  return btor_sext_exp (btor, exp, width);
}

BtorExp *
boolector_implies (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != 1 || BTOR_REAL_ADDR_EXP (e1)->len != 1,
      "bit-width of 'e0' and 'e1' must not be unequal to 1");
  btor->external_refs++;
  return btor_implies_exp (btor, e0, e1);
}

BtorExp *
boolector_iff (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len != 1 || BTOR_REAL_ADDR_EXP (e1)->len != 1,
      "bit-width of 'e0' and 'e1' must not be unequal to 1");
  btor->external_refs++;
  return btor_iff_exp (btor, e0, e1);
}

BtorExp *
boolector_xor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_xor_exp (btor, e0, e1);
}

BtorExp *
boolector_xnor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_xnor_exp (btor, e0, e1);
}

BtorExp *
boolector_and (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_and_exp (btor, e0, e1);
}

BtorExp *
boolector_nand (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_nand_exp (btor, e0, e1);
}

BtorExp *
boolector_or (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_or_exp (btor, e0, e1);
}

BtorExp *
boolector_nor (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_nor_exp (btor, e0, e1);
}

BtorExp *
boolector_eq (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0          = btor_pointer_chase_simplified_exp (btor, e0);
  e1          = btor_pointer_chase_simplified_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  BTOR_ABORT_BOOLECTOR (is_array_e0 != is_array_e1,
                        "array must not be compared to bit-vector");
  BTOR_ABORT_BOOLECTOR (!is_array_e0 && real_e0->len != real_e1->len,
                        "bit-vectors must not have unequal bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->len != real_e1->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->index_len != real_e1->index_len,
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  return btor_eq_exp (btor, e0, e1);
}

BtorExp *
boolector_ne (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0          = btor_pointer_chase_simplified_exp (btor, e0);
  e1          = btor_pointer_chase_simplified_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  BTOR_ABORT_BOOLECTOR (is_array_e0 != is_array_e1,
                        "array must not be compared to bit-vector");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->len != real_e1->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_e0 && real_e0->index_len != real_e1->index_len,
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  return btor_ne_exp (btor, e0, e1);
}

BtorExp *
boolector_add (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_add_exp (btor, e0, e1);
}

BtorExp *
boolector_uaddo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_uaddo_exp (btor, e0, e1);
}

BtorExp *
boolector_saddo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_saddo_exp (btor, e0, e1);
}

BtorExp *
boolector_mul (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_mul_exp (btor, e0, e1);
}

BtorExp *
boolector_umulo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_umulo_exp (btor, e0, e1);
}

BtorExp *
boolector_smulo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_smulo_exp (btor, e0, e1);
}

BtorExp *
boolector_ult (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_ult_exp (btor, e0, e1);
}

BtorExp *
boolector_slt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_slt_exp (btor, e0, e1);
}

BtorExp *
boolector_ulte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_ulte_exp (btor, e0, e1);
}

BtorExp *
boolector_slte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_slte_exp (btor, e0, e1);
}

BtorExp *
boolector_ugt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_ugt_exp (btor, e0, e1);
}

BtorExp *
boolector_sgt (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_sgt_exp (btor, e0, e1);
}

BtorExp *
boolector_ugte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_ugte_exp (btor, e0, e1);
}

BtorExp *
boolector_sgte (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_sgte_exp (btor, e0, e1);
}

BtorExp *
boolector_sll (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  return btor_sll_exp (btor, e0, e1);
}

BtorExp *
boolector_srl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  return btor_srl_exp (btor, e0, e1);
}

BtorExp *
boolector_sra (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  return btor_sra_exp (btor, e0, e1);
}

BtorExp *
boolector_rol (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  return btor_rol_exp (btor, e0, e1);
}

BtorExp *
boolector_ror (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  return btor_ror_exp (btor, e0, e1);
}

BtorExp *
boolector_sub (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_sub_exp (btor, e0, e1);
}

BtorExp *
boolector_usubo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_usubo_exp (btor, e0, e1);
}

BtorExp *
boolector_ssubo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_ssubo_exp (btor, e0, e1);
}

BtorExp *
boolector_udiv (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_udiv_exp (btor, e0, e1);
}

BtorExp *
boolector_sdiv (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_sdiv_exp (btor, e0, e1);
}

BtorExp *
boolector_sdivo (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_sdivo_exp (btor, e0, e1);
}

BtorExp *
boolector_urem (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_urem_exp (btor, e0, e1);
}

BtorExp *
boolector_srem (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_srem_exp (btor, e0, e1);
}

BtorExp *
boolector_smod (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_NE_BW (e0, e1);
  btor->external_refs++;
  return btor_smod_exp (btor, e0, e1);
}

BtorExp *
boolector_concat (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (e0);
  BTOR_ABORT_ARRAY_BOOLECTOR (e1);
  BTOR_ABORT_BOOLECTOR (
      BTOR_REAL_ADDR_EXP (e0)->len > INT_MAX - BTOR_REAL_ADDR_EXP (e1)->len,
      "bit-width of result is too large");
  btor->external_refs++;
  return btor_concat_exp (btor, e0, e1);
}

BtorExp *
boolector_read (Btor *btor, BtorExp *e_array, BtorExp *e_index)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_index);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_index);
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  BTOR_ABORT_BV_BOLECTOR (e_array);
  BTOR_ABORT_ARRAY_BOOLECTOR (e_index);
  BTOR_ABORT_BOOLECTOR (e_array->index_len != BTOR_REAL_ADDR_EXP (e_index)->len,
                        "index bit-width of 'e_array' and bit-width of "
                        "'e_index' must not be unequal");
  btor->external_refs++;
  return btor_read_exp (btor, e_array, e_index);
}

BtorExp *
boolector_write (Btor *btor,
                 BtorExp *e_array,
                 BtorExp *e_index,
                 BtorExp *e_value)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_index);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_value);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_index);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_value);
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  e_value = btor_pointer_chase_simplified_exp (btor, e_value);
  BTOR_ABORT_BV_BOLECTOR (e_array);
  BTOR_ABORT_ARRAY_BOOLECTOR (e_index);
  BTOR_ABORT_ARRAY_BOOLECTOR (e_value);
  BTOR_ABORT_BOOLECTOR (e_array->index_len != BTOR_REAL_ADDR_EXP (e_index)->len,
                        "index bit-width of 'e_array' and bit-width of "
                        "'e_index' must not be unequal");
  BTOR_ABORT_BOOLECTOR (e_array->len != BTOR_REAL_ADDR_EXP (e_value)->len,
                        "element bit-width of 'e_array' and bit-width of "
                        "'e_value' must not be unequal");
  btor->external_refs++;
  return btor_write_exp (btor, e_array, e_index, e_value);
}

BtorExp *
boolector_cond (Btor *btor, BtorExp *e_cond, BtorExp *e_if, BtorExp *e_else)
{
  BtorExp *real_e_if, *real_e_else;
  int is_array_e_if, is_array_e_else;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_cond);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_if);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_else);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_cond);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_if);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_else);
  e_cond = btor_pointer_chase_simplified_exp (btor, e_cond);
  e_if   = btor_pointer_chase_simplified_exp (btor, e_if);
  e_else = btor_pointer_chase_simplified_exp (btor, e_else);
  BTOR_ABORT_ARRAY_BOOLECTOR (e_cond);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_EXP (e_cond)->len != 1,
                        "bit-width of 'e_cond' must be equal to 1");
  real_e_if       = BTOR_REAL_ADDR_EXP (e_if);
  real_e_else     = BTOR_REAL_ADDR_EXP (e_else);
  is_array_e_if   = BTOR_IS_ARRAY_EXP (real_e_if);
  is_array_e_else = BTOR_IS_ARRAY_EXP (real_e_else);
  BTOR_ABORT_BOOLECTOR (is_array_e_if != is_array_e_else,
                        "array must not be combined with bit-vector");
  BTOR_ABORT_BOOLECTOR (!is_array_e_if && real_e_if->len != real_e_else->len,
                        "bit-vectors must not have unequal bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_e_if && real_e_if->len != real_e_else->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (
      is_array_e_if && real_e_if->index_len != real_e_else->index_len,
      "arrays must not have unequal index bit-width");
  btor->external_refs++;
  return btor_cond_exp (btor, e_cond, e_if, e_else);
}

BtorExp *
boolector_inc (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);

  btor->external_refs++;
  return btor_inc_exp (btor, exp);
}

BtorExp *
boolector_dec (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);

  btor->external_refs++;
  return btor_dec_exp (btor, exp);
}

int
boolector_get_width (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  return btor_get_exp_len (btor, exp);
}

int
boolector_is_array (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return btor_is_array_exp (btor, exp);
}

int
boolector_get_width_index (Btor *btor, BtorExp *e_array)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  BTOR_ABORT_BV_BOLECTOR (e_array);
  return btor_get_index_exp_len (btor, e_array);
}

const char *
boolector_get_symbol_of_var (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  return (const char *) btor_get_symbol_exp (btor, exp);
}

BtorExp *
boolector_copy (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor->external_refs++;
  return btor_copy_exp (btor, exp);
}

void
boolector_release (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor->external_refs--;
  btor_release_exp (btor, exp);
}

void
boolector_dump_btor (Btor *btor, FILE *file, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor_dump_exp (btor, file, exp);
}

void
boolector_dump_smt (Btor *btor, FILE *file, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  btor_dump_smt (btor, file, exp);
}

void
boolector_assert (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_EXP (exp)->len != 1,
                        "'exp' must have bit-width one");
  btor_add_constraint_exp (btor, exp);
}

void
boolector_assume (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (!btor->inc_enabled,
                        "incremental usage has not been enabled");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_EXP (exp)->len != 1,
                        "'exp' must have bit-width one");
  btor_add_assumption_exp (btor, exp);
}

int
boolector_sat (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (!btor->inc_enabled && btor->btor_sat_btor_called > 0,
                        "incremental usage has not been enabled. "
                        "'boolector_sat' may only be called once");
  return btor_sat_btor (btor);
}

char *
boolector_bv_assignment (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (!btor->model_gen,
                        "model generation has not been enabled");
  return btor_bv_assignment_exp (btor, exp);
}

void
boolector_array_assignment (
    Btor *btor, BtorExp *e_array, char ***indices, char ***values, int *size)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (indices);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (values);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (size);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  BTOR_ABORT_BV_BOLECTOR (e_array);
  BTOR_ABORT_BOOLECTOR (!btor->model_gen,
                        "model generation has not been enabled");
  btor_array_assignment_exp (btor, e_array, indices, values, size);
}

void
boolector_free_bv_assignment (Btor *btor, char *assignment)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (assignment);
  btor_free_bv_assignment_exp (btor, assignment);
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/

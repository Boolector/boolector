/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testexp.h"
#include "btorcore.h"
#include "dumper/btordumpbtor.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static Btor *g_btor = NULL;

void
init_exp_tests (void)
{
}

void
init_exp_test (void)
{
  g_btor = btor_new_btor ();
  if (g_rwreads) btor_set_opt (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
}

void
finish_exp_test (void)
{
  btor_delete_btor (g_btor);
}

static void
test_new_delete_btor (void)
{
  init_exp_test ();
  finish_exp_test ();
}

static void
test_const_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorBitVector *bv1, *bv2, *bv3;

  init_exp_test ();

  bv1  = btor_bv_char_to_bv (g_btor->mm, "00010011");
  bv2  = btor_bv_char_to_bv (g_btor->mm, "00010011");
  bv3  = btor_bv_char_to_bv (g_btor->mm, "0000000000010011");
  exp1 = btor_const_exp (g_btor, bv1);
  exp2 = btor_const_exp (g_btor, bv2);
  exp3 = btor_const_exp (g_btor, bv3);
  assert (exp1 == exp2);
  assert (exp2 != exp3);
  assert (btor_get_exp_width (g_btor, exp1) == 8);
  assert (btor_get_exp_width (g_btor, exp2) == 8);
  assert (btor_get_exp_width (g_btor, exp3) == 16);
  btor_dump_btor_node (g_btor, g_logfile, exp2);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_bv_free (g_btor->mm, bv1);
  btor_bv_free (g_btor->mm, bv2);
  btor_bv_free (g_btor->mm, bv3);
  finish_exp_test ();
}

static void
test_zero_exp (void)
{
  BtorNode *exp1, *exp2;
  BtorBitVector *bv2;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);
  exp1 = btor_zero_exp (g_btor, sort);
  btor_release_sort (g_btor, sort);
  bv2  = btor_bv_new (g_btor->mm, 8);
  exp2 = btor_const_exp (g_btor, bv2);
  assert (exp1 == exp2);
  assert (btor_get_exp_width (g_btor, exp1) == 8);
  assert (btor_get_exp_width (g_btor, exp2) == 8);
  btor_dump_btor_node (g_btor, g_logfile, exp1);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_bv_free (g_btor->mm, bv2);
  finish_exp_test ();
}

static void
test_ones_exp (void)
{
  BtorNode *exp1, *exp2;
  BtorBitVector *bv2;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);
  exp1 = btor_ones_exp (g_btor, sort);
  btor_release_sort (g_btor, sort);
  bv2  = btor_bv_ones (g_btor->mm, 8);
  exp2 = btor_const_exp (g_btor, bv2);
  assert (exp1 == exp2);
  assert (btor_get_exp_width (g_btor, exp1) == 8);
  assert (btor_get_exp_width (g_btor, exp2) == 8);
  btor_dump_btor_node (g_btor, g_logfile, exp1);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_bv_free (g_btor->mm, bv2);
  finish_exp_test ();
}

static void
test_one_exp (void)
{
  BtorNode *exp1, *exp2;
  BtorBitVector *bv2;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);
  exp1 = btor_one_exp (g_btor, sort);
  btor_release_sort (g_btor, sort);
  bv2  = btor_bv_one (g_btor->mm, 8);
  exp2 = btor_const_exp (g_btor, bv2);
  assert (exp1 == exp2);
  assert (btor_get_exp_width (g_btor, exp1) == 8);
  assert (btor_get_exp_width (g_btor, exp2) == 8);
  btor_dump_btor_node (g_btor, g_logfile, exp1);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_bv_free (g_btor->mm, bv2);
  finish_exp_test ();
}

static void
test_unsigned_to_exp (void)
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6, *exp7, *exp8;
  BtorBitVector *bv5, *bv6, *bv7, *bv8;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);
  exp1 = btor_unsigned_exp (g_btor, 32u, sort);
  exp2 = btor_unsigned_exp (g_btor, 49u, sort);
  exp3 = btor_unsigned_exp (g_btor, 3u, sort);
  exp4 = btor_unsigned_exp (g_btor, 57u, sort);
  btor_release_sort (g_btor, sort);
  bv5  = btor_bv_char_to_bv (g_btor->mm, "00100000");
  bv6  = btor_bv_char_to_bv (g_btor->mm, "00110001");
  bv7  = btor_bv_char_to_bv (g_btor->mm, "00000011");
  bv8  = btor_bv_char_to_bv (g_btor->mm, "00111001");
  exp5 = btor_const_exp (g_btor, bv5);
  exp6 = btor_const_exp (g_btor, bv6);
  exp7 = btor_const_exp (g_btor, bv7);
  exp8 = btor_const_exp (g_btor, bv8);

  assert (exp1 == exp5);
  assert (exp2 == exp6);
  assert (exp3 == exp7);
  assert (exp4 == exp8);
  assert (btor_get_exp_width (g_btor, exp1) == 8);
  assert (btor_get_exp_width (g_btor, exp2) == 8);
  assert (btor_get_exp_width (g_btor, exp3) == 8);
  assert (btor_get_exp_width (g_btor, exp4) == 8);
  assert (btor_get_exp_width (g_btor, exp5) == 8);
  assert (btor_get_exp_width (g_btor, exp6) == 8);
  assert (btor_get_exp_width (g_btor, exp7) == 8);
  assert (btor_get_exp_width (g_btor, exp8) == 8);
  btor_dump_btor_node (g_btor, g_logfile, exp4);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_release_exp (g_btor, exp4);
  btor_release_exp (g_btor, exp5);
  btor_release_exp (g_btor, exp6);
  btor_release_exp (g_btor, exp7);
  btor_release_exp (g_btor, exp8);
  btor_bv_free (g_btor->mm, bv5);
  btor_bv_free (g_btor->mm, bv6);
  btor_bv_free (g_btor->mm, bv7);
  btor_bv_free (g_btor->mm, bv8);
  finish_exp_test ();
}

static void
test_var_exp (void)
{
  BtorNode *exp1, *exp2;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);

  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = btor_copy_exp (g_btor, exp1);

  assert (exp1 == exp2);
  assert (btor_get_exp_width (g_btor, exp1) == 8);
  assert (btor_get_exp_width (g_btor, exp2) == 8);
  btor_dump_btor_node (g_btor, g_logfile, exp2);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  finish_exp_test ();
}

static void
test_array_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId index_sort, elem_sort, array_sort;

  init_exp_test ();

  elem_sort  = btor_bitvec_sort (g_btor, 32);
  index_sort = btor_bitvec_sort (g_btor, 8);
  array_sort = btor_array_sort (g_btor, index_sort, elem_sort);
  exp1       = btor_array_exp (g_btor, array_sort, "array1");
  exp2       = btor_copy_exp (g_btor, exp1);
  exp3       = btor_array_exp (g_btor, array_sort, "array2");
  btor_release_sort (g_btor, elem_sort);
  btor_release_sort (g_btor, index_sort);
  btor_release_sort (g_btor, array_sort);

  assert (exp1 == exp2);
  assert (exp1 != exp3);
  assert (btor_get_fun_exp_width (g_btor, exp1) == 32);
  assert (btor_get_fun_exp_width (g_btor, exp2) == 32);
  assert (btor_get_fun_exp_width (g_btor, exp3) == 32);
  assert (btor_get_index_exp_width (g_btor, exp1) == 8);
  assert (btor_get_index_exp_width (g_btor, exp2) == 8);
  assert (btor_get_index_exp_width (g_btor, exp3) == 8);
  btor_dump_btor_node (g_btor, g_logfile, exp2);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  finish_exp_test ();
}

static void
unary_exp_test (BtorNode *(*func) (Btor *, BtorNode *) )
{
  const unsigned len = 8;
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);
  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = func (g_btor, exp1);
  exp3 = func (g_btor, exp1);

  assert (exp2 == exp3);
  assert (btor_get_exp_width (g_btor, exp1) == len);
  if (func == btor_not_exp || func == btor_neg_exp)
  {
    assert (btor_get_exp_width (g_btor, exp2) == len);
    assert (btor_get_exp_width (g_btor, exp3) == len);
  }
  else
  {
    assert (btor_get_exp_width (g_btor, exp2) == 1);
    assert (btor_get_exp_width (g_btor, exp3) == 1);
  }
  btor_dump_btor_node (g_btor, g_logfile, exp3);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  finish_exp_test ();
}

static void
test_not_exp (void)
{
  unary_exp_test (btor_not_exp);
}

static void
test_neg_exp (void)
{
  unary_exp_test (btor_neg_exp);
}

static void
test_redor_exp (void)
{
  unary_exp_test (btor_redor_exp);
}

static void
test_redxor_exp (void)
{
  unary_exp_test (btor_redxor_exp);
}

static void
test_redand_exp (void)
{
  unary_exp_test (btor_redand_exp);
}

static void
test_slice_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 32);

  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = btor_slice_exp (g_btor, exp1, 31, 30);
  exp3 = btor_slice_exp (g_btor, exp1, 31, 30);

  assert (exp2 == exp3);
  btor_dump_btor_node (g_btor, g_logfile, exp3);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  finish_exp_test ();
}

static void
ext_exp_test (BtorNode *(*func) (Btor *, BtorNode *, uint32_t))
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 32);

  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = func (g_btor, exp1, 32);
  exp3 = func (g_btor, exp1, 32);

  assert (exp2 == exp3);
  btor_dump_btor_node (g_btor, g_logfile, exp3);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  finish_exp_test ();
}

static void
test_uext_exp (void)
{
  ext_exp_test (btor_uext_exp);
}

static void
test_sext_exp (void)
{
  ext_exp_test (btor_sext_exp);
}

static void
binary_commutative_exp_test (BtorNode *(*func) (Btor *,
                                                BtorNode *,
                                                BtorNode *) )
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);

  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = btor_var_exp (g_btor, sort, "v2");
  exp3 = func (g_btor, exp1, exp2);
  exp4 = func (g_btor, exp1, exp2);
  exp5 = func (g_btor, exp2, exp1);

  assert (exp3 == exp4);
  assert (exp4 == exp5);
  assert (btor_get_exp_width (g_btor, exp1) == 8);
  assert (btor_get_exp_width (g_btor, exp2) == 8);
  if (func == btor_eq_exp || func == btor_ne_exp || func == btor_uaddo_exp
      || func == btor_saddo_exp || func == btor_umulo_exp)
  {
    assert (btor_get_exp_width (g_btor, exp3) == 1);
    assert (btor_get_exp_width (g_btor, exp4) == 1);
    assert (btor_get_exp_width (g_btor, exp5) == 1);
  }
  else
  {
    assert (btor_get_exp_width (g_btor, exp3) == 8);
    assert (btor_get_exp_width (g_btor, exp4) == 8);
    assert (btor_get_exp_width (g_btor, exp5) == 8);
  }
  btor_dump_btor_node (g_btor, g_logfile, exp3);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_release_exp (g_btor, exp4);
  btor_release_exp (g_btor, exp5);
  finish_exp_test ();
}

static void
test_or_exp (void)
{
  binary_commutative_exp_test (btor_or_exp);
}

static void
test_xor_exp (void)
{
  binary_commutative_exp_test (btor_xor_exp);
}

static void
test_xnor_exp (void)
{
  binary_commutative_exp_test (btor_xnor_exp);
}

static void
test_and_exp (void)
{
  binary_commutative_exp_test (btor_and_exp);
}

static void
test_eq_exp (void)
{
  binary_commutative_exp_test (btor_eq_exp);
}

static void
test_ne_exp (void)
{
  binary_commutative_exp_test (btor_ne_exp);
}

static void
test_add_exp (void)
{
  binary_commutative_exp_test (btor_add_exp);
}

static void
test_uaddo_exp (void)
{
  binary_commutative_exp_test (btor_uaddo_exp);
}

static void
test_saddo_exp (void)
{
  binary_commutative_exp_test (btor_saddo_exp);
}

static void
test_mul_exp (void)
{
  binary_commutative_exp_test (btor_mul_exp);
}

static void
binary_non_commutative_exp_test (BtorNode *(*func) (Btor *,
                                                    BtorNode *,
                                                    BtorNode *) )
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 32);
  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = btor_var_exp (g_btor, sort, "v2");
  exp3 = func (g_btor, exp1, exp2);
  exp4 = func (g_btor, exp1, exp2);
  exp5 = func (g_btor, exp2, exp1);

  assert (exp3 == exp4);
  assert (exp4 != exp5);
  if (func == btor_sub_exp || func == btor_udiv_exp || func == btor_sdiv_exp
      || func == btor_urem_exp || func == btor_srem_exp
      || func == btor_smod_exp)
  {
    assert (btor_get_exp_width (g_btor, exp3) == 32);
    assert (btor_get_exp_width (g_btor, exp4) == 32);
    assert (btor_get_exp_width (g_btor, exp5) == 32);
  }
  else if (func == btor_concat_exp)
  {
    assert (btor_get_exp_width (g_btor, exp3) == 64);
    assert (btor_get_exp_width (g_btor, exp4) == 64);
    assert (btor_get_exp_width (g_btor, exp5) == 64);
  }
  else
  {
    assert (btor_get_exp_width (g_btor, exp3) == 1);
    assert (btor_get_exp_width (g_btor, exp4) == 1);
    assert (btor_get_exp_width (g_btor, exp5) == 1);
  }
  btor_dump_btor_node (g_btor, g_logfile, exp4);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_release_exp (g_btor, exp4);
  btor_release_exp (g_btor, exp5);
  finish_exp_test ();
}

static void
test_ult_exp (void)
{
  binary_non_commutative_exp_test (btor_ult_exp);
}

static void
test_slt_exp (void)
{
  binary_non_commutative_exp_test (btor_slt_exp);
}

static void
test_ulte_exp (void)
{
  binary_non_commutative_exp_test (btor_ulte_exp);
}

static void
test_slte_exp (void)
{
  binary_non_commutative_exp_test (btor_slte_exp);
}

static void
test_ugt_exp (void)
{
  binary_non_commutative_exp_test (btor_ugt_exp);
}

static void
test_sgt_exp (void)
{
  binary_non_commutative_exp_test (btor_sgt_exp);
}

static void
test_ugte_exp (void)
{
  binary_non_commutative_exp_test (btor_ugte_exp);
}

static void
test_sgte_exp (void)
{
  binary_non_commutative_exp_test (btor_sgte_exp);
}

static void
test_sub_exp (void)
{
  binary_non_commutative_exp_test (btor_sub_exp);
}

static void
test_usubo_exp (void)
{
  binary_non_commutative_exp_test (btor_usubo_exp);
}

static void
test_ssubo_exp (void)
{
  binary_non_commutative_exp_test (btor_ssubo_exp);
}

static void
test_udiv_exp (void)
{
  binary_non_commutative_exp_test (btor_udiv_exp);
}

static void
test_sdiv_exp (void)
{
  binary_non_commutative_exp_test (btor_sdiv_exp);
}

static void
test_sdivo_exp (void)
{
  binary_non_commutative_exp_test (btor_sdivo_exp);
}

static void
test_urem_exp (void)
{
  binary_non_commutative_exp_test (btor_urem_exp);
}

static void
test_srem_exp (void)
{
  binary_non_commutative_exp_test (btor_srem_exp);
}

static void
test_smod_exp (void)
{
  binary_non_commutative_exp_test (btor_smod_exp);
}

static void
test_concat_exp (void)
{
  binary_non_commutative_exp_test (btor_concat_exp);
}

static void
mulo_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 3);

  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = btor_var_exp (g_btor, sort, "v2");
  exp3 = func (g_btor, exp1, exp2);
  exp4 = func (g_btor, exp1, exp2);
  exp5 = func (g_btor, exp2, exp1);

  assert (exp3 == exp4);
  if (func == btor_umulo_exp)
    assert (exp4 != exp5);
  else
    assert (exp4 == exp5);
  assert (btor_get_exp_width (g_btor, exp3) == 1);
  assert (btor_get_exp_width (g_btor, exp4) == 1);
  assert (btor_get_exp_width (g_btor, exp5) == 1);
  btor_dump_btor_node (g_btor, g_logfile, exp4);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_release_exp (g_btor, exp4);
  btor_release_exp (g_btor, exp5);
  btor_release_sort (g_btor, sort);
  finish_exp_test ();
}

static void
test_umulo_exp (void)
{
  /* Implementation is not symmetric */
  mulo_exp_test (btor_umulo_exp);
}

static void
test_smulo_exp (void)
{
  mulo_exp_test (btor_smulo_exp);
}

static void
shift_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
{
  BtorNode *exp1, *exp2, *exp3, *exp4;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 32);
  exp1 = btor_var_exp (g_btor, sort, "v1");
  btor_release_sort (g_btor, sort);
  sort = btor_bitvec_sort (g_btor, 5);
  exp2 = btor_var_exp (g_btor, sort, "v2");
  btor_release_sort (g_btor, sort);
  exp3 = func (g_btor, exp1, exp2);
  exp4 = func (g_btor, exp1, exp2);

  assert (exp3 == exp4);
  assert (btor_get_exp_width (g_btor, exp1) == 32);
  assert (btor_get_exp_width (g_btor, exp2) == 5);
  assert (btor_get_exp_width (g_btor, exp3) == 32);
  assert (btor_get_exp_width (g_btor, exp4) == 32);
  btor_dump_btor_node (g_btor, g_logfile, exp4);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_release_exp (g_btor, exp4);
  finish_exp_test ();
}

static void
test_sll_exp (void)
{
  shift_exp_test (btor_sll_exp);
}

static void
test_srl_exp (void)
{
  shift_exp_test (btor_srl_exp);
}

static void
test_sra_exp (void)
{
  shift_exp_test (btor_sra_exp);
}

static void
test_rol_exp (void)
{
  shift_exp_test (btor_rol_exp);
}

static void
test_ror_exp (void)
{
  shift_exp_test (btor_ror_exp);
}

static void
test_read_exp (void)
{
  BtorNode *exp1, *exp2, *exp3, *exp4;
  BtorSortId elem_sort, index_sort, array_sort;

  init_exp_test ();

  elem_sort  = btor_bitvec_sort (g_btor, 32);
  index_sort = btor_bitvec_sort (g_btor, 8);
  array_sort = btor_array_sort (g_btor, index_sort, elem_sort);

  init_exp_test ();

  exp1 = btor_array_exp (g_btor, array_sort, "array1");
  exp2 = btor_var_exp (g_btor, index_sort, "v1");
  exp3 = btor_read_exp (g_btor, exp1, exp2);
  exp4 = btor_read_exp (g_btor, exp1, exp2);

  assert (exp4 == exp3);
  assert (btor_get_fun_exp_width (g_btor, exp1) == 32);
  assert (btor_get_index_exp_width (g_btor, exp1) == 8);
  assert (btor_get_exp_width (g_btor, exp2) == 8);
  assert (btor_get_exp_width (g_btor, exp3) == 32);
  assert (btor_get_exp_width (g_btor, exp4) == 32);
  btor_dump_btor_node (g_btor, g_logfile, exp4);
  btor_release_sort (g_btor, index_sort);
  btor_release_sort (g_btor, elem_sort);
  btor_release_sort (g_btor, array_sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_release_exp (g_btor, exp4);
  finish_exp_test ();
}

static void
test_cond_exp (void)
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6;
  BtorBitVector *bv3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 1);
  exp1 = btor_var_exp (g_btor, sort, "v1");
  btor_release_sort (g_btor, sort);
  sort = btor_bitvec_sort (g_btor, 32);
  exp2 = btor_var_exp (g_btor, sort, "v2");
  btor_release_sort (g_btor, sort);
  bv3  = btor_bv_char_to_bv (g_btor->mm, "00110111001101010001010100110100");
  exp3 = btor_const_exp (g_btor, bv3);
  exp4 = btor_cond_exp (g_btor, exp1, exp2, exp3);
  exp5 = btor_cond_exp (g_btor, exp1, exp2, exp3);
  exp6 = btor_cond_exp (g_btor, exp1, exp3, exp2);

  assert (exp4 == exp5);
  assert (exp4 != exp6);
  assert (btor_get_exp_width (g_btor, exp1) == 1);
  assert (btor_get_exp_width (g_btor, exp2) == 32);
  assert (btor_get_exp_width (g_btor, exp3) == 32);
  assert (btor_get_exp_width (g_btor, exp4) == 32);
  assert (btor_get_exp_width (g_btor, exp5) == 32);
  assert (btor_get_exp_width (g_btor, exp6) == 32);
  btor_dump_btor_node (g_btor, g_logfile, exp4);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_release_exp (g_btor, exp4);
  btor_release_exp (g_btor, exp5);
  btor_release_exp (g_btor, exp6);
  btor_bv_free (g_btor->mm, bv3);
  finish_exp_test ();
}

static void
test_write_exp (void)
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6, *exp7;
  BtorSortId sort, array_sort;

  init_exp_test ();

  sort       = btor_bitvec_sort (g_btor, 1);
  array_sort = btor_array_sort (g_btor, sort, sort);
  exp1       = btor_array_exp (g_btor, array_sort, "array1");
  exp2       = btor_var_exp (g_btor, sort, "v1");
  exp3       = btor_var_exp (g_btor, sort, "v2");
  exp4       = btor_write_exp (g_btor, exp1, exp2, exp3);
  exp5       = btor_write_exp (g_btor, exp1, exp2, exp3);
  exp6       = btor_write_exp (g_btor, exp1, exp3, exp2);
  exp7       = btor_read_exp (g_btor, exp5, exp2);

  assert (exp4 == exp5);
  assert (exp4 != exp6);
  assert (btor_get_fun_exp_width (g_btor, exp1) == 1);
  assert (btor_get_exp_width (g_btor, exp2) == 1);
  assert (btor_get_exp_width (g_btor, exp3) == 1);
  assert (btor_get_fun_exp_width (g_btor, exp4) == 1);
  assert (btor_get_fun_exp_width (g_btor, exp5) == 1);
  assert (btor_get_fun_exp_width (g_btor, exp6) == 1);
  assert (btor_get_exp_width (g_btor, exp7) == 1);
  btor_dump_btor_node (g_btor, g_logfile, exp7);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  btor_release_exp (g_btor, exp4);
  btor_release_exp (g_btor, exp5);
  btor_release_exp (g_btor, exp6);
  btor_release_exp (g_btor, exp7);
  finish_exp_test ();
}

static void
test_inc_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);

  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = btor_inc_exp (g_btor, exp1);
  exp3 = btor_inc_exp (g_btor, exp1);

  assert (exp2 == exp3);
  btor_dump_btor_node (g_btor, g_logfile, exp3);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  finish_exp_test ();
}

static void
test_dec_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_bitvec_sort (g_btor, 8);

  exp1 = btor_var_exp (g_btor, sort, "v1");
  exp2 = btor_dec_exp (g_btor, exp1);
  exp3 = btor_dec_exp (g_btor, exp1);

  assert (exp2 == exp3);
  btor_dump_btor_node (g_btor, g_logfile, exp3);
  btor_release_sort (g_btor, sort);
  btor_release_exp (g_btor, exp1);
  btor_release_exp (g_btor, exp2);
  btor_release_exp (g_btor, exp3);
  finish_exp_test ();
}

void
run_exp_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_btor);
  BTOR_RUN_TEST_CHECK_LOG (const_exp);
  BTOR_RUN_TEST_CHECK_LOG (zero_exp);
  BTOR_RUN_TEST_CHECK_LOG (ones_exp);
  BTOR_RUN_TEST_CHECK_LOG (one_exp);
  BTOR_RUN_TEST_CHECK_LOG (unsigned_to_exp);
  BTOR_RUN_TEST_CHECK_LOG (var_exp);
  BTOR_RUN_TEST_CHECK_LOG (array_exp);
  BTOR_RUN_TEST_CHECK_LOG (not_exp);
  BTOR_RUN_TEST_CHECK_LOG (neg_exp);
  BTOR_RUN_TEST_CHECK_LOG (redor_exp);
  BTOR_RUN_TEST_CHECK_LOG (redxor_exp);
  BTOR_RUN_TEST_CHECK_LOG (redand_exp);
  BTOR_RUN_TEST_CHECK_LOG (slice_exp);
  BTOR_RUN_TEST_CHECK_LOG (uext_exp);
  BTOR_RUN_TEST_CHECK_LOG (sext_exp);
  BTOR_RUN_TEST_CHECK_LOG (or_exp);
  BTOR_RUN_TEST_CHECK_LOG (xor_exp);
  BTOR_RUN_TEST_CHECK_LOG (xnor_exp);
  BTOR_RUN_TEST_CHECK_LOG (and_exp);
  BTOR_RUN_TEST_CHECK_LOG (eq_exp);
  BTOR_RUN_TEST_CHECK_LOG (ne_exp);
  BTOR_RUN_TEST_CHECK_LOG (add_exp);
  BTOR_RUN_TEST_CHECK_LOG (uaddo_exp);
  BTOR_RUN_TEST_CHECK_LOG (saddo_exp);
  BTOR_RUN_TEST_CHECK_LOG (mul_exp);
  BTOR_RUN_TEST_CHECK_LOG (ult_exp);
  BTOR_RUN_TEST_CHECK_LOG (slt_exp);
  BTOR_RUN_TEST_CHECK_LOG (ulte_exp);
  BTOR_RUN_TEST_CHECK_LOG (slte_exp);
  BTOR_RUN_TEST_CHECK_LOG (ugt_exp);
  BTOR_RUN_TEST_CHECK_LOG (sgt_exp);
  BTOR_RUN_TEST_CHECK_LOG (ugte_exp);
  BTOR_RUN_TEST_CHECK_LOG (sgte_exp);
  BTOR_RUN_TEST_CHECK_LOG (umulo_exp);
  BTOR_RUN_TEST_CHECK_LOG (smulo_exp);
  BTOR_RUN_TEST_CHECK_LOG (sll_exp);
  BTOR_RUN_TEST_CHECK_LOG (srl_exp);
  BTOR_RUN_TEST_CHECK_LOG (sra_exp);
  BTOR_RUN_TEST_CHECK_LOG (rol_exp);
  BTOR_RUN_TEST_CHECK_LOG (ror_exp);
  BTOR_RUN_TEST_CHECK_LOG (sub_exp);
  BTOR_RUN_TEST_CHECK_LOG (usubo_exp);
  BTOR_RUN_TEST_CHECK_LOG (ssubo_exp);
  BTOR_RUN_TEST_CHECK_LOG (udiv_exp);
  BTOR_RUN_TEST_CHECK_LOG (sdiv_exp);
  BTOR_RUN_TEST_CHECK_LOG (sdivo_exp);
  BTOR_RUN_TEST_CHECK_LOG (urem_exp);
  BTOR_RUN_TEST_CHECK_LOG (srem_exp);
  BTOR_RUN_TEST_CHECK_LOG (smod_exp);
  BTOR_RUN_TEST_CHECK_LOG (concat_exp);
  BTOR_RUN_TEST_CHECK_LOG (read_exp);
  BTOR_RUN_TEST_CHECK_LOG (cond_exp);
  BTOR_RUN_TEST_CHECK_LOG (write_exp);
  BTOR_RUN_TEST_CHECK_LOG (inc_exp);
  BTOR_RUN_TEST_CHECK_LOG (dec_exp);
}

void
finish_exp_tests (void)
{
}

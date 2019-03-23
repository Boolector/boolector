/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testexp.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btornode.h"
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
  g_btor = btor_new ();
  if (g_rwreads) btor_opt_set (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
}

void
finish_exp_test (void)
{
  btor_delete (g_btor);
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
  exp1 = btor_exp_bv_const (g_btor, bv1);
  exp2 = btor_exp_bv_const (g_btor, bv2);
  exp3 = btor_exp_bv_const (g_btor, bv3);
  assert (exp1 == exp2);
  assert (exp2 != exp3);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  assert (btor_node_bv_get_width (g_btor, exp3) == 16);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp2);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
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

  sort = btor_sort_bv (g_btor, 8);
  exp1 = btor_exp_bv_zero (g_btor, sort);
  btor_sort_release (g_btor, sort);
  bv2  = btor_bv_new (g_btor->mm, 8);
  exp2 = btor_exp_bv_const (g_btor, bv2);
  assert (exp1 == exp2);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  assert (!btor_node_is_bv_const_one (g_btor, exp1));
  assert (!btor_node_is_bv_const_one (g_btor, exp2));
  assert (!btor_node_is_bv_const_one (g_btor, btor_node_invert (exp1)));
  assert (!btor_node_is_bv_const_one (g_btor, btor_node_invert (exp2)));
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp1);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
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

  sort = btor_sort_bv (g_btor, 8);
  exp1 = btor_exp_bv_ones (g_btor, sort);
  btor_sort_release (g_btor, sort);
  bv2  = btor_bv_ones (g_btor->mm, 8);
  exp2 = btor_exp_bv_const (g_btor, bv2);
  assert (exp1 == exp2);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  assert (!btor_node_is_bv_const_one (g_btor, exp1));
  assert (!btor_node_is_bv_const_one (g_btor, exp2));
  assert (!btor_node_is_bv_const_one (g_btor, btor_node_invert (exp1)));
  assert (!btor_node_is_bv_const_one (g_btor, btor_node_invert (exp2)));
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp1);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_bv_free (g_btor->mm, bv2);
  finish_exp_test ();
}

static void
test_one_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorBitVector *bv2, *bv3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 8);
  exp1 = btor_exp_bv_one (g_btor, sort);
  btor_sort_release (g_btor, sort);
  bv2  = btor_bv_one (g_btor->mm, 8);
  exp2 = btor_exp_bv_const (g_btor, bv2);
  assert (exp1 == exp2);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  assert (btor_node_is_bv_const_one (g_btor, exp1));
  assert (btor_node_is_bv_const_one (g_btor, exp2));
  assert (!btor_node_is_bv_const_one (g_btor, btor_node_invert (exp1)));
  assert (!btor_node_is_bv_const_one (g_btor, btor_node_invert (exp2)));
  bv3  = btor_bv_char_to_bv (g_btor->mm, "11111110");
  exp3 = btor_exp_bv_const (g_btor, bv3);
  assert (!btor_node_is_bv_const_one (g_btor, exp3));
  assert (btor_node_is_bv_const_one (g_btor, btor_node_invert (exp3)));
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp1);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_bv_free (g_btor->mm, bv2);
  btor_bv_free (g_btor->mm, bv3);
  finish_exp_test ();
}

static void
test_min_signed_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorBitVector *bv2, *bv3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 8);
  exp1 = btor_exp_bv_min_signed (g_btor, sort);
  btor_sort_release (g_btor, sort);
  bv2  = btor_bv_min_signed (g_btor->mm, 8);
  exp2 = btor_exp_bv_const (g_btor, bv2);
  assert (exp1 == exp2);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  assert (btor_node_is_bv_const_min_signed (g_btor, exp1));
  assert (btor_node_is_bv_const_min_signed (g_btor, exp2));
  assert (!btor_node_is_bv_const_min_signed (g_btor, btor_node_invert (exp1)));
  assert (!btor_node_is_bv_const_min_signed (g_btor, btor_node_invert (exp2)));
  bv3  = btor_bv_char_to_bv (g_btor->mm, "01111111");
  exp3 = btor_exp_bv_const (g_btor, bv3);
  assert (!btor_node_is_bv_const_min_signed (g_btor, exp3));
  assert (btor_node_is_bv_const_min_signed (g_btor, btor_node_invert (exp3)));
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp1);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_bv_free (g_btor->mm, bv2);
  btor_bv_free (g_btor->mm, bv3);
  finish_exp_test ();
}

static void
test_max_signed_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorBitVector *bv2, *bv3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 8);
  exp1 = btor_exp_bv_max_signed (g_btor, sort);
  btor_sort_release (g_btor, sort);
  bv2  = btor_bv_max_signed (g_btor->mm, 8);
  exp2 = btor_exp_bv_const (g_btor, bv2);
  assert (exp1 == exp2);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  assert (btor_node_is_bv_const_max_signed (g_btor, exp1));
  assert (btor_node_is_bv_const_max_signed (g_btor, exp2));
  assert (!btor_node_is_bv_const_max_signed (g_btor, btor_node_invert (exp1)));
  assert (!btor_node_is_bv_const_max_signed (g_btor, btor_node_invert (exp2)));
  bv3  = btor_bv_char_to_bv (g_btor->mm, "10000000");
  exp3 = btor_exp_bv_const (g_btor, bv3);
  assert (!btor_node_is_bv_const_max_signed (g_btor, exp3));
  assert (btor_node_is_bv_const_max_signed (g_btor, btor_node_invert (exp3)));
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp1);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_bv_free (g_btor->mm, bv2);
  btor_bv_free (g_btor->mm, bv3);
  finish_exp_test ();
}

static void
test_unsigned_to_exp (void)
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6, *exp7, *exp8;
  BtorBitVector *bv5, *bv6, *bv7, *bv8;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 8);
  exp1 = btor_exp_bv_unsigned (g_btor, 32u, sort);
  exp2 = btor_exp_bv_unsigned (g_btor, 49u, sort);
  exp3 = btor_exp_bv_unsigned (g_btor, 3u, sort);
  exp4 = btor_exp_bv_unsigned (g_btor, 57u, sort);
  btor_sort_release (g_btor, sort);
  bv5  = btor_bv_char_to_bv (g_btor->mm, "00100000");
  bv6  = btor_bv_char_to_bv (g_btor->mm, "00110001");
  bv7  = btor_bv_char_to_bv (g_btor->mm, "00000011");
  bv8  = btor_bv_char_to_bv (g_btor->mm, "00111001");
  exp5 = btor_exp_bv_const (g_btor, bv5);
  exp6 = btor_exp_bv_const (g_btor, bv6);
  exp7 = btor_exp_bv_const (g_btor, bv7);
  exp8 = btor_exp_bv_const (g_btor, bv8);

  assert (exp1 == exp5);
  assert (exp2 == exp6);
  assert (exp3 == exp7);
  assert (exp4 == exp8);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  assert (btor_node_bv_get_width (g_btor, exp3) == 8);
  assert (btor_node_bv_get_width (g_btor, exp4) == 8);
  assert (btor_node_bv_get_width (g_btor, exp5) == 8);
  assert (btor_node_bv_get_width (g_btor, exp6) == 8);
  assert (btor_node_bv_get_width (g_btor, exp7) == 8);
  assert (btor_node_bv_get_width (g_btor, exp8) == 8);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp4);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_node_release (g_btor, exp4);
  btor_node_release (g_btor, exp5);
  btor_node_release (g_btor, exp6);
  btor_node_release (g_btor, exp7);
  btor_node_release (g_btor, exp8);
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

  sort = btor_sort_bv (g_btor, 8);

  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = btor_node_copy (g_btor, exp1);

  assert (exp1 == exp2);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp2);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  finish_exp_test ();
}

static void
test_array_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId index_sort, elem_sort, array_sort;

  init_exp_test ();

  elem_sort  = btor_sort_bv (g_btor, 32);
  index_sort = btor_sort_bv (g_btor, 8);
  array_sort = btor_sort_array (g_btor, index_sort, elem_sort);
  exp1       = btor_exp_array (g_btor, array_sort, "array1");
  exp2       = btor_node_copy (g_btor, exp1);
  exp3       = btor_exp_array (g_btor, array_sort, "array2");
  btor_sort_release (g_btor, elem_sort);
  btor_sort_release (g_btor, index_sort);
  btor_sort_release (g_btor, array_sort);

  assert (exp1 == exp2);
  assert (exp1 != exp3);
  assert (btor_node_fun_get_width (g_btor, exp1) == 32);
  assert (btor_node_fun_get_width (g_btor, exp2) == 32);
  assert (btor_node_fun_get_width (g_btor, exp3) == 32);
  assert (btor_node_array_get_index_width (g_btor, exp1) == 8);
  assert (btor_node_array_get_index_width (g_btor, exp2) == 8);
  assert (btor_node_array_get_index_width (g_btor, exp3) == 8);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp2);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  finish_exp_test ();
}

static void
unary_exp_test (BtorNode *(*func) (Btor *, BtorNode *) )
{
  const uint32_t len = 8;
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 8);
  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = func (g_btor, exp1);
  exp3 = func (g_btor, exp1);

  assert (exp2 == exp3);
  assert (btor_node_bv_get_width (g_btor, exp1) == len);
  if (func == btor_exp_bv_not || func == btor_exp_bv_neg)
  {
    assert (btor_node_bv_get_width (g_btor, exp2) == len);
    assert (btor_node_bv_get_width (g_btor, exp3) == len);
    if (func == btor_exp_bv_neg)
    {
      assert (btor_node_is_neg (g_btor, exp2, 0));
      assert (btor_node_is_neg (g_btor, exp3, 0));
    }
    else
    {
      assert (!btor_node_is_neg (g_btor, exp2, 0));
      assert (!btor_node_is_neg (g_btor, exp3, 0));
    }
  }
  else
  {
    assert (btor_node_bv_get_width (g_btor, exp2) == 1);
    assert (btor_node_bv_get_width (g_btor, exp3) == 1);
  }
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp3);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  finish_exp_test ();
}

static void
test_not_exp (void)
{
  unary_exp_test (btor_exp_bv_not);
}

static void
test_neg_exp (void)
{
  unary_exp_test (btor_exp_bv_neg);
}

static void
test_redor_exp (void)
{
  unary_exp_test (btor_exp_bv_redor);
}

static void
test_redxor_exp (void)
{
  unary_exp_test (btor_exp_bv_redxor);
}

static void
test_redand_exp (void)
{
  unary_exp_test (btor_exp_bv_redand);
}

static void
test_slice_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 32);

  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = btor_exp_bv_slice (g_btor, exp1, 31, 30);
  exp3 = btor_exp_bv_slice (g_btor, exp1, 31, 30);

  assert (exp2 == exp3);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp3);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  finish_exp_test ();
}

static void
ext_exp_test (BtorNode *(*func) (Btor *, BtorNode *, uint32_t))
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 32);

  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = func (g_btor, exp1, 32);
  exp3 = func (g_btor, exp1, 32);

  assert (exp2 == exp3);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp3);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  finish_exp_test ();
}

static void
test_uext_exp (void)
{
  ext_exp_test (btor_exp_bv_uext);
}

static void
test_sext_exp (void)
{
  ext_exp_test (btor_exp_bv_sext);
}

static void
binary_commutative_exp_test (BtorNode *(*func) (Btor *,
                                                BtorNode *,
                                                BtorNode *) )
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 8);

  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = btor_exp_var (g_btor, sort, "v2");
  exp3 = func (g_btor, exp1, exp2);
  exp4 = func (g_btor, exp1, exp2);
  exp5 = func (g_btor, exp2, exp1);

  assert (exp3 == exp4);
  assert (exp4 == exp5);
  assert (btor_node_bv_get_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  if (func == btor_exp_eq || func == btor_exp_ne || func == btor_exp_bv_uaddo
      || func == btor_exp_bv_saddo || func == btor_exp_bv_umulo)
  {
    assert (btor_node_bv_get_width (g_btor, exp3) == 1);
    assert (btor_node_bv_get_width (g_btor, exp4) == 1);
    assert (btor_node_bv_get_width (g_btor, exp5) == 1);
  }
  else
  {
    assert (btor_node_bv_get_width (g_btor, exp3) == 8);
    assert (btor_node_bv_get_width (g_btor, exp4) == 8);
    assert (btor_node_bv_get_width (g_btor, exp5) == 8);
  }
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp3);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_node_release (g_btor, exp4);
  btor_node_release (g_btor, exp5);
  finish_exp_test ();
}

static void
test_or_exp (void)
{
  binary_commutative_exp_test (btor_exp_bv_or);
}

static void
test_xor_exp (void)
{
  binary_commutative_exp_test (btor_exp_bv_xor);
}

static void
test_xnor_exp (void)
{
  binary_commutative_exp_test (btor_exp_bv_xnor);
}

static void
test_and_exp (void)
{
  binary_commutative_exp_test (btor_exp_bv_and);
}

static void
test_eq_exp (void)
{
  binary_commutative_exp_test (btor_exp_eq);
}

static void
test_ne_exp (void)
{
  binary_commutative_exp_test (btor_exp_ne);
}

static void
test_add_exp (void)
{
  binary_commutative_exp_test (btor_exp_bv_add);
}

static void
test_uaddo_exp (void)
{
  binary_commutative_exp_test (btor_exp_bv_uaddo);
}

static void
test_saddo_exp (void)
{
  binary_commutative_exp_test (btor_exp_bv_saddo);
}

static void
test_mul_exp (void)
{
  binary_commutative_exp_test (btor_exp_bv_mul);
}

static void
binary_non_commutative_exp_test (BtorNode *(*func) (Btor *,
                                                    BtorNode *,
                                                    BtorNode *) )
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 32);
  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = btor_exp_var (g_btor, sort, "v2");
  exp3 = func (g_btor, exp1, exp2);
  exp4 = func (g_btor, exp1, exp2);
  exp5 = func (g_btor, exp2, exp1);

  assert (exp3 == exp4);
  assert (exp4 != exp5);
  if (func == btor_exp_bv_sub || func == btor_exp_bv_udiv
      || func == btor_exp_bv_sdiv || func == btor_exp_bv_urem
      || func == btor_exp_bv_srem || func == btor_exp_bv_smod)
  {
    assert (btor_node_bv_get_width (g_btor, exp3) == 32);
    assert (btor_node_bv_get_width (g_btor, exp4) == 32);
    assert (btor_node_bv_get_width (g_btor, exp5) == 32);
  }
  else if (func == btor_exp_bv_concat)
  {
    assert (btor_node_bv_get_width (g_btor, exp3) == 64);
    assert (btor_node_bv_get_width (g_btor, exp4) == 64);
    assert (btor_node_bv_get_width (g_btor, exp5) == 64);
  }
  else
  {
    assert (btor_node_bv_get_width (g_btor, exp3) == 1);
    assert (btor_node_bv_get_width (g_btor, exp4) == 1);
    assert (btor_node_bv_get_width (g_btor, exp5) == 1);
  }
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp4);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_node_release (g_btor, exp4);
  btor_node_release (g_btor, exp5);
  finish_exp_test ();
}

static void
test_ult_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_ult);
}

static void
test_slt_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_slt);
}

static void
test_ulte_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_ulte);
}

static void
test_slte_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_slte);
}

static void
test_ugt_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_ugt);
}

static void
test_sgt_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_sgt);
}

static void
test_ugte_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_ugte);
}

static void
test_sgte_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_sgte);
}

static void
test_sub_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_sub);
}

static void
test_usubo_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_usubo);
}

static void
test_ssubo_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_ssubo);
}

static void
test_udiv_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_udiv);
}

static void
test_sdiv_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_sdiv);
}

static void
test_sdivo_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_sdivo);
}

static void
test_urem_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_urem);
}

static void
test_srem_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_srem);
}

static void
test_smod_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_smod);
}

static void
test_concat_exp (void)
{
  binary_non_commutative_exp_test (btor_exp_bv_concat);
}

static void
mulo_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 3);

  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = btor_exp_var (g_btor, sort, "v2");
  exp3 = func (g_btor, exp1, exp2);
  exp4 = func (g_btor, exp1, exp2);
  exp5 = func (g_btor, exp2, exp1);

  assert (exp3 == exp4);
  if (func == btor_exp_bv_umulo)
    assert (exp4 != exp5);
  else
    assert (exp4 == exp5);
  assert (btor_node_bv_get_width (g_btor, exp3) == 1);
  assert (btor_node_bv_get_width (g_btor, exp4) == 1);
  assert (btor_node_bv_get_width (g_btor, exp5) == 1);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp4);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_node_release (g_btor, exp4);
  btor_node_release (g_btor, exp5);
  btor_sort_release (g_btor, sort);
  finish_exp_test ();
}

static void
test_umulo_exp (void)
{
  /* Implementation is not symmetric */
  mulo_exp_test (btor_exp_bv_umulo);
}

static void
test_smulo_exp (void)
{
  mulo_exp_test (btor_exp_bv_smulo);
}

static void
shift_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
{
  BtorNode *exp1, *exp2, *exp3, *exp4;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 32);
  exp1 = btor_exp_var (g_btor, sort, "v1");
  btor_sort_release (g_btor, sort);
  sort = btor_sort_bv (g_btor, 5);
  exp2 = btor_exp_var (g_btor, sort, "v2");
  btor_sort_release (g_btor, sort);
  exp3 = func (g_btor, exp1, exp2);
  exp4 = func (g_btor, exp1, exp2);

  assert (exp3 == exp4);
  assert (btor_node_bv_get_width (g_btor, exp1) == 32);
  assert (btor_node_bv_get_width (g_btor, exp2) == 5);
  assert (btor_node_bv_get_width (g_btor, exp3) == 32);
  assert (btor_node_bv_get_width (g_btor, exp4) == 32);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp4);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_node_release (g_btor, exp4);
  finish_exp_test ();
}

static void
test_sll_exp (void)
{
  shift_exp_test (btor_exp_bv_sll);
}

static void
test_srl_exp (void)
{
  shift_exp_test (btor_exp_bv_srl);
}

static void
test_sra_exp (void)
{
  shift_exp_test (btor_exp_bv_sra);
}

static void
test_rol_exp (void)
{
  shift_exp_test (btor_exp_bv_rol);
}

static void
test_ror_exp (void)
{
  shift_exp_test (btor_exp_bv_ror);
}

static void
test_read_exp (void)
{
  BtorNode *exp1, *exp2, *exp3, *exp4;
  BtorSortId elem_sort, index_sort, array_sort;

  init_exp_test ();

  elem_sort  = btor_sort_bv (g_btor, 32);
  index_sort = btor_sort_bv (g_btor, 8);
  array_sort = btor_sort_array (g_btor, index_sort, elem_sort);

  init_exp_test ();

  exp1 = btor_exp_array (g_btor, array_sort, "array1");
  exp2 = btor_exp_var (g_btor, index_sort, "v1");
  exp3 = btor_exp_read (g_btor, exp1, exp2);
  exp4 = btor_exp_read (g_btor, exp1, exp2);

  assert (exp4 == exp3);
  assert (btor_node_fun_get_width (g_btor, exp1) == 32);
  assert (btor_node_array_get_index_width (g_btor, exp1) == 8);
  assert (btor_node_bv_get_width (g_btor, exp2) == 8);
  assert (btor_node_bv_get_width (g_btor, exp3) == 32);
  assert (btor_node_bv_get_width (g_btor, exp4) == 32);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp4);
  btor_sort_release (g_btor, index_sort);
  btor_sort_release (g_btor, elem_sort);
  btor_sort_release (g_btor, array_sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_node_release (g_btor, exp4);
  finish_exp_test ();
}

static void
test_cond_exp (void)
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6;
  BtorBitVector *bv3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 1);
  exp1 = btor_exp_var (g_btor, sort, "v1");
  btor_sort_release (g_btor, sort);
  sort = btor_sort_bv (g_btor, 32);
  exp2 = btor_exp_var (g_btor, sort, "v2");
  btor_sort_release (g_btor, sort);
  bv3  = btor_bv_char_to_bv (g_btor->mm, "00110111001101010001010100110100");
  exp3 = btor_exp_bv_const (g_btor, bv3);
  exp4 = btor_exp_cond (g_btor, exp1, exp2, exp3);
  exp5 = btor_exp_cond (g_btor, exp1, exp2, exp3);
  exp6 = btor_exp_cond (g_btor, exp1, exp3, exp2);

  assert (exp4 == exp5);
  assert (exp4 != exp6);
  assert (btor_node_bv_get_width (g_btor, exp1) == 1);
  assert (btor_node_bv_get_width (g_btor, exp2) == 32);
  assert (btor_node_bv_get_width (g_btor, exp3) == 32);
  assert (btor_node_bv_get_width (g_btor, exp4) == 32);
  assert (btor_node_bv_get_width (g_btor, exp5) == 32);
  assert (btor_node_bv_get_width (g_btor, exp6) == 32);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp4);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_node_release (g_btor, exp4);
  btor_node_release (g_btor, exp5);
  btor_node_release (g_btor, exp6);
  btor_bv_free (g_btor->mm, bv3);
  finish_exp_test ();
}

static void
test_write_exp (void)
{
  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6, *exp7;
  BtorSortId sort, array_sort;

  init_exp_test ();

  sort       = btor_sort_bv (g_btor, 1);
  array_sort = btor_sort_array (g_btor, sort, sort);
  exp1       = btor_exp_array (g_btor, array_sort, "array1");
  exp2       = btor_exp_var (g_btor, sort, "v1");
  exp3       = btor_exp_var (g_btor, sort, "v2");
  exp4       = btor_exp_write (g_btor, exp1, exp2, exp3);
  exp5       = btor_exp_write (g_btor, exp1, exp2, exp3);
  exp6       = btor_exp_write (g_btor, exp1, exp3, exp2);
  exp7       = btor_exp_read (g_btor, exp5, exp2);

  assert (exp4 == exp5);
  assert (exp4 != exp6);
  assert (btor_node_fun_get_width (g_btor, exp1) == 1);
  assert (btor_node_bv_get_width (g_btor, exp2) == 1);
  assert (btor_node_bv_get_width (g_btor, exp3) == 1);
  assert (btor_node_fun_get_width (g_btor, exp4) == 1);
  assert (btor_node_fun_get_width (g_btor, exp5) == 1);
  assert (btor_node_fun_get_width (g_btor, exp6) == 1);
  assert (btor_node_bv_get_width (g_btor, exp7) == 1);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp7);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  btor_node_release (g_btor, exp4);
  btor_node_release (g_btor, exp5);
  btor_node_release (g_btor, exp6);
  btor_node_release (g_btor, exp7);
  finish_exp_test ();
}

static void
test_inc_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 8);

  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = btor_exp_bv_inc (g_btor, exp1);
  exp3 = btor_exp_bv_inc (g_btor, exp1);

  assert (exp2 == exp3);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp3);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  finish_exp_test ();
}

static void
test_dec_exp (void)
{
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  init_exp_test ();

  sort = btor_sort_bv (g_btor, 8);

  exp1 = btor_exp_var (g_btor, sort, "v1");
  exp2 = btor_exp_bv_dec (g_btor, exp1);
  exp3 = btor_exp_bv_dec (g_btor, exp1);

  assert (exp2 == exp3);
  btor_dumpbtor_dump_node (g_btor, g_logfile, exp3);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, exp1);
  btor_node_release (g_btor, exp2);
  btor_node_release (g_btor, exp3);
  finish_exp_test ();
}

void
run_exp_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_btor);
  BTOR_RUN_TEST_CHECK_LOG (const_exp);
  BTOR_RUN_TEST_CHECK_LOG (zero_exp);
  BTOR_RUN_TEST_CHECK_LOG (ones_exp);
  BTOR_RUN_TEST_CHECK_LOG (one_exp);
  BTOR_RUN_TEST_CHECK_LOG (min_signed_exp);
  BTOR_RUN_TEST_CHECK_LOG (max_signed_exp);
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

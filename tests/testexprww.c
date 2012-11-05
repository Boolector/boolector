/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2007-2012 Robert Daniel Brummayer, Armin Biere
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "testexprww.h"
#include "btorexp.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

void
init_exp_rww_tests (void)
{
}

static void
test_new_delete_btor (void)
{
  Btor *btor = btor_new_btor ();
  btor_delete_btor (btor);
}

static void
test_const_exp_rww (void)
{
  FILE *fout     = fopen ("log/const_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_const_exp (btor, "00010011");
  BtorNode *exp2 = btor_const_exp (btor, "00010011");
  BtorNode *exp3 = btor_const_exp (btor, "0000000000010011");
  assert (exp1 == exp2);
  assert (exp2 != exp3);
  assert (btor_get_exp_len (btor, exp1) == 8);
  assert (btor_get_exp_len (btor, exp2) == 8);
  assert (btor_get_exp_len (btor, exp3) == 16);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp2);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_zero_exp_rww (void)
{
  FILE *fout     = fopen ("log/zero_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_zero_exp (btor, 8);
  BtorNode *exp2 = btor_const_exp (btor, "00000000");
  assert (exp1 == exp2);
  assert (btor_get_exp_len (btor, exp1) == 8);
  assert (btor_get_exp_len (btor, exp2) == 8);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp1);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_ones_exp_rww (void)
{
  FILE *fout     = fopen ("log/ones_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_ones_exp (btor, 8);
  BtorNode *exp2 = btor_const_exp (btor, "11111111");
  assert (exp1 == exp2);
  assert (btor_get_exp_len (btor, exp1) == 8);
  assert (btor_get_exp_len (btor, exp2) == 8);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp1);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_one_exp_rww (void)
{
  FILE *fout     = fopen ("log/one_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_one_exp (btor, 8);
  BtorNode *exp2 = btor_const_exp (btor, "00000001");
  assert (exp1 == exp2);
  assert (btor_get_exp_len (btor, exp1) == 8);
  assert (btor_get_exp_len (btor, exp2) == 8);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp1);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_unsigned_to_exp_rww (void)
{
  FILE *fout     = fopen ("log/unsigned_to_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_unsigned_to_exp (btor, 32u, 8);
  BtorNode *exp2 = btor_unsigned_to_exp (btor, 49u, 8);
  BtorNode *exp3 = btor_unsigned_to_exp (btor, 3u, 8);
  BtorNode *exp4 = btor_unsigned_to_exp (btor, 57u, 8);
  BtorNode *exp5 = btor_const_exp (btor, "00100000");
  BtorNode *exp6 = btor_const_exp (btor, "00110001");
  BtorNode *exp7 = btor_const_exp (btor, "00000011");
  BtorNode *exp8 = btor_const_exp (btor, "00111001");
  assert (exp1 == exp5);
  assert (exp2 == exp6);
  assert (exp3 == exp7);
  assert (exp4 == exp8);
  assert (btor_get_exp_len (btor, exp1) == 8);
  assert (btor_get_exp_len (btor, exp2) == 8);
  assert (btor_get_exp_len (btor, exp3) == 8);
  assert (btor_get_exp_len (btor, exp4) == 8);
  assert (btor_get_exp_len (btor, exp5) == 8);
  assert (btor_get_exp_len (btor, exp6) == 8);
  assert (btor_get_exp_len (btor, exp7) == 8);
  assert (btor_get_exp_len (btor, exp8) == 8);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp4);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_release_exp (btor, exp4);
  btor_release_exp (btor, exp5);
  btor_release_exp (btor, exp6);
  btor_release_exp (btor, exp7);
  btor_release_exp (btor, exp8);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_var_exp_rww (void)
{
  FILE *fout     = fopen ("log/var_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 8, "v1");
  BtorNode *exp2 = btor_copy_exp (btor, exp1);
  assert (exp1 == exp2);
  assert (btor_get_exp_len (btor, exp1) == 8);
  assert (btor_get_exp_len (btor, exp2) == 8);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp2);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_array_exp_rww (void)
{
  FILE *fout     = fopen ("log/array_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_array_exp (btor, 32, 8, "array1");
  BtorNode *exp2 = btor_copy_exp (btor, exp1);
  BtorNode *exp3 = btor_array_exp (btor, 32, 8, "array2");
  assert (exp1 == exp2);
  assert (exp1 != exp3);
  assert (btor_get_exp_len (btor, exp1) == 32);
  assert (btor_get_exp_len (btor, exp2) == 32);
  assert (btor_get_exp_len (btor, exp3) == 32);
  assert (btor_get_index_exp_len (btor, exp1) == 8);
  assert (btor_get_index_exp_len (btor, exp2) == 8);
  assert (btor_get_index_exp_len (btor, exp3) == 8);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp2);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
unary_exp_test (BtorNode *(*func) (Btor *, BtorNode *), char *log)
{
  FILE *fout     = fopen (log, "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 8, "v1");
  BtorNode *exp2 = func (btor, exp1);
  BtorNode *exp3 = func (btor, exp1);
  assert (exp2 == exp3);
  assert (btor_get_exp_len (btor, exp1) == 8);
  if (func == btor_not_exp || func == btor_neg_exp)
  {
    assert (btor_get_exp_len (btor, exp2) == 8);
    assert (btor_get_exp_len (btor, exp3) == 8);
  }
  else
  {
    assert (btor_get_exp_len (btor, exp2) == 1);
    assert (btor_get_exp_len (btor, exp3) == 1);
  }
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp3);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_not_exp_rww (void)
{
  unary_exp_test (btor_not_exp, "log/not_exp_rww.log");
}

static void
test_neg_exp_rww (void)
{
  unary_exp_test (btor_neg_exp, "log/neg_exp_rww.log");
}

static void
test_redor_exp_rww (void)
{
  unary_exp_test (btor_redor_exp, "log/redor_exp_rww.log");
}

static void
test_redxor_exp_rww (void)
{
  unary_exp_test (btor_redxor_exp, "log/redxor_exp_rww.log");
}

static void
test_redand_exp_rww (void)
{
  unary_exp_test (btor_redand_exp, "log/redand_exp_rww.log");
}

static void
test_slice_exp_rww (void)
{
  FILE *fout     = fopen ("log/slice_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 32, "v1");
  BtorNode *exp2 = btor_slice_exp (btor, exp1, 31, 30);
  BtorNode *exp3 = btor_slice_exp (btor, exp1, 31, 30);
  assert (exp2 == exp3);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp3);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
ext_exp_test (BtorNode *(*func) (Btor *, BtorNode *, int), char *log)
{
  FILE *fout     = fopen (log, "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 32, "v1");
  BtorNode *exp2 = func (btor, exp1, 32);
  BtorNode *exp3 = func (btor, exp1, 32);
  assert (exp2 == exp3);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp3);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_uext_exp_rww (void)
{
  ext_exp_test (btor_uext_exp, "log/uext_exp_rww.log");
}

static void
test_sext_exp_rww (void)
{
  ext_exp_test (btor_sext_exp, "log/sext_exp_rww.log");
}

static void
binary_commutative_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *),
                             char *log)
{
  FILE *fout     = fopen (log, "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 8, "v1");
  BtorNode *exp2 = btor_var_exp (btor, 8, "v2");
  BtorNode *exp3 = func (btor, exp1, exp2);
  BtorNode *exp4 = func (btor, exp1, exp2);
  BtorNode *exp5 = func (btor, exp2, exp1);
  assert (exp3 == exp4);
  assert (exp4 == exp5);
  assert (btor_get_exp_len (btor, exp1) == 8);
  assert (btor_get_exp_len (btor, exp2) == 8);
  if (func == btor_eq_exp || func == btor_ne_exp || func == btor_uaddo_exp
      || func == btor_saddo_exp || func == btor_umulo_exp)
  {
    assert (btor_get_exp_len (btor, exp3) == 1);
    assert (btor_get_exp_len (btor, exp4) == 1);
    assert (btor_get_exp_len (btor, exp5) == 1);
  }
  else
  {
    assert (btor_get_exp_len (btor, exp3) == 8);
    assert (btor_get_exp_len (btor, exp4) == 8);
    assert (btor_get_exp_len (btor, exp5) == 8);
  }
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp3);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_release_exp (btor, exp4);
  btor_release_exp (btor, exp5);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_or_exp_rww (void)
{
  binary_commutative_exp_test (btor_or_exp, "log/or_exp_rww.log");
}

static void
test_xor_exp_rww (void)
{
  binary_commutative_exp_test (btor_xor_exp, "log/xor_exp_rww.log");
}

static void
test_xnor_exp_rww (void)
{
  binary_commutative_exp_test (btor_xnor_exp, "log/xnor_exp_rww.log");
}

static void
test_and_exp_rww (void)
{
  binary_commutative_exp_test (btor_and_exp, "log/and_exp_rww.log");
}

static void
test_eq_exp_rww (void)
{
  binary_commutative_exp_test (btor_eq_exp, "log/eq_exp_rww.log");
}

static void
test_ne_exp_rww (void)
{
  binary_commutative_exp_test (btor_ne_exp, "log/ne_exp_rww.log");
}

static void
test_add_exp_rww (void)
{
  binary_commutative_exp_test (btor_add_exp, "log/add_exp_rww.log");
}

static void
test_uaddo_exp_rww (void)
{
  binary_commutative_exp_test (btor_uaddo_exp, "log/uaddo_exp_rww.log");
}

static void
test_saddo_exp_rww (void)
{
  binary_commutative_exp_test (btor_saddo_exp, "log/saddo_exp_rww.log");
}

static void
test_mul_exp_rww (void)
{
  binary_commutative_exp_test (btor_mul_exp, "log/mul_exp_rww.log");
}

static void
binary_non_commutative_exp_test (
    BtorNode *(*func) (Btor *, BtorNode *, BtorNode *), char *log)
{
  FILE *fout     = fopen (log, "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 32, "v1");
  BtorNode *exp2 = btor_var_exp (btor, 32, "v2");
  BtorNode *exp3 = func (btor, exp1, exp2);
  BtorNode *exp4 = func (btor, exp1, exp2);
  BtorNode *exp5 = func (btor, exp2, exp1);
  assert (exp3 == exp4);
  assert (exp4 != exp5);
  if (func == btor_sub_exp || func == btor_udiv_exp || func == btor_sdiv_exp
      || func == btor_urem_exp || func == btor_srem_exp
      || func == btor_smod_exp)
  {
    assert (btor_get_exp_len (btor, exp3) == 32);
    assert (btor_get_exp_len (btor, exp4) == 32);
    assert (btor_get_exp_len (btor, exp5) == 32);
  }
  else if (func == btor_concat_exp)
  {
    assert (btor_get_exp_len (btor, exp3) == 64);
    assert (btor_get_exp_len (btor, exp4) == 64);
    assert (btor_get_exp_len (btor, exp5) == 64);
  }
  else
  {
    assert (btor_get_exp_len (btor, exp3) == 1);
    assert (btor_get_exp_len (btor, exp4) == 1);
    assert (btor_get_exp_len (btor, exp5) == 1);
  }
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp4);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_release_exp (btor, exp4);
  btor_release_exp (btor, exp5);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_ult_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_ult_exp, "log/ult_exp_rww.log");
}

static void
test_slt_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_slt_exp, "log/slt_exp_rww.log");
}

static void
test_ulte_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_ulte_exp, "log/ulte_exp_rww.log");
}

static void
test_slte_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_slte_exp, "log/slte_exp_rww.log");
}

static void
test_ugt_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_ugt_exp, "log/ugt_exp_rww.log");
}

static void
test_sgt_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_sgt_exp, "log/sgt_exp_rww.log");
}

static void
test_ugte_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_ugte_exp, "log/ugte_exp_rww.log");
}

static void
test_sgte_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_sgte_exp, "log/sgte_exp_rww.log");
}

static void
test_sub_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_sub_exp, "log/sub_exp_rww.log");
}

static void
test_usubo_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_usubo_exp, "log/usubo_exp_rww.log");
}

static void
test_ssubo_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_ssubo_exp, "log/ssubo_exp_rww.log");
}

static void
test_udiv_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_udiv_exp, "log/udiv_exp_rww.log");
}

static void
test_sdiv_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_sdiv_exp, "log/sdiv_exp_rww.log");
}

static void
test_sdivo_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_sdivo_exp, "log/sdivo_exp_rww.log");
}

static void
test_urem_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_urem_exp, "log/urem_exp_rww.log");
}

static void
test_srem_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_srem_exp, "log/srem_exp_rww.log");
}

static void
test_smod_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_smod_exp, "log/smod_exp_rww.log");
}

static void
test_concat_exp_rww (void)
{
  binary_non_commutative_exp_test (btor_concat_exp, "log/concat_exp_rww.log");
}

static void
mulo_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *), char *log)
{
  FILE *fout     = fopen (log, "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 3, "v1");
  BtorNode *exp2 = btor_var_exp (btor, 3, "v2");
  BtorNode *exp3 = func (btor, exp1, exp2);
  BtorNode *exp4 = func (btor, exp1, exp2);
  BtorNode *exp5 = func (btor, exp2, exp1);
  assert (exp3 == exp4);
  if (func == btor_umulo_exp)
    assert (exp4 != exp5);
  else
    assert (exp4 == exp5);
  assert (btor_get_exp_len (btor, exp3) == 1);
  assert (btor_get_exp_len (btor, exp4) == 1);
  assert (btor_get_exp_len (btor, exp5) == 1);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp4);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_release_exp (btor, exp4);
  btor_release_exp (btor, exp5);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_umulo_exp_rww (void)
{
  /* Implementation is not symmetric */
  mulo_exp_test (btor_umulo_exp, "log/umulo_exp_rww.log");
}

static void
test_smulo_exp_rww (void)
{
  mulo_exp_test (btor_smulo_exp, "log/smulo_exp_rww.log");
}

static void
shift_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *), char *log)
{
  FILE *fout     = fopen (log, "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 32, "v1");
  BtorNode *exp2 = btor_var_exp (btor, 5, "v2");
  BtorNode *exp3 = func (btor, exp1, exp2);
  BtorNode *exp4 = func (btor, exp1, exp2);
  assert (exp3 == exp4);
  assert (btor_get_exp_len (btor, exp1) == 32);
  assert (btor_get_exp_len (btor, exp2) == 5);
  assert (btor_get_exp_len (btor, exp3) == 32);
  assert (btor_get_exp_len (btor, exp4) == 32);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp4);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_release_exp (btor, exp4);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_sll_exp_rww (void)
{
  shift_exp_test (btor_sll_exp, "log/sll_exp_rww.log");
}

static void
test_srl_exp_rww (void)
{
  shift_exp_test (btor_srl_exp, "log/srl_exp_rww.log");
}

static void
test_sra_exp_rww (void)
{
  shift_exp_test (btor_sra_exp, "log/sra_exp_rww.log");
}

static void
test_rol_exp_rww (void)
{
  shift_exp_test (btor_rol_exp, "log/rol_exp_rww.log");
}

static void
test_ror_exp_rww (void)
{
  shift_exp_test (btor_ror_exp, "log/ror_exp_rww.log");
}

static void
test_read_exp_rww (void)
{
  FILE *fout     = fopen ("log/read_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_array_exp (btor, 32, 8, "array1");
  BtorNode *exp2 = btor_var_exp (btor, 8, "v1");
  BtorNode *exp3 = btor_read_exp (btor, exp1, exp2);
  BtorNode *exp4 = btor_read_exp (btor, exp1, exp2);
  assert (exp4 == exp3);
  assert (btor_get_exp_len (btor, exp1) == 32);
  assert (btor_get_index_exp_len (btor, exp1) == 8);
  assert (btor_get_exp_len (btor, exp2) == 8);
  assert (btor_get_exp_len (btor, exp3) == 32);
  assert (btor_get_exp_len (btor, exp4) == 32);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp4);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_release_exp (btor, exp4);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_cond_exp_rww (void)
{
  FILE *fout     = fopen ("log/cond_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 1, "v1");
  BtorNode *exp2 = btor_var_exp (btor, 32, "v2");
  BtorNode *exp3 = btor_const_exp (btor, "00110111001101010001010100110100");
  BtorNode *exp4 = btor_cond_exp (btor, exp1, exp2, exp3);
  BtorNode *exp5 = btor_cond_exp (btor, exp1, exp2, exp3);
  BtorNode *exp6 = btor_cond_exp (btor, exp1, exp3, exp2);
  assert (exp4 == exp5);
  assert (exp4 != exp6);
  assert (btor_get_exp_len (btor, exp1) == 1);
  assert (btor_get_exp_len (btor, exp2) == 32);
  assert (btor_get_exp_len (btor, exp3) == 32);
  assert (btor_get_exp_len (btor, exp4) == 32);
  assert (btor_get_exp_len (btor, exp5) == 32);
  assert (btor_get_exp_len (btor, exp6) == 32);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp4);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_release_exp (btor, exp4);
  btor_release_exp (btor, exp5);
  btor_release_exp (btor, exp6);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_write_exp_rww (void)
{
  FILE *fout     = fopen ("log/write_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_array_exp (btor, 1, 1, "array1");
  BtorNode *exp2 = btor_var_exp (btor, 1, "v1");
  BtorNode *exp3 = btor_var_exp (btor, 1, "v2");
  BtorNode *exp4 = btor_write_exp (btor, exp1, exp2, exp3);
  BtorNode *exp5 = btor_write_exp (btor, exp1, exp2, exp3);
  BtorNode *exp6 = btor_write_exp (btor, exp1, exp3, exp2);
  BtorNode *exp7 = btor_read_exp (btor, exp5, exp2);
  assert (exp4 == exp5);
  assert (exp4 != exp6);
  assert (btor_get_exp_len (btor, exp1) == 1);
  assert (btor_get_exp_len (btor, exp2) == 1);
  assert (btor_get_exp_len (btor, exp3) == 1);
  assert (btor_get_exp_len (btor, exp4) == 1);
  assert (btor_get_exp_len (btor, exp5) == 1);
  assert (btor_get_exp_len (btor, exp6) == 1);
  assert (btor_get_exp_len (btor, exp7) == 1);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp7);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_release_exp (btor, exp4);
  btor_release_exp (btor, exp5);
  btor_release_exp (btor, exp6);
  btor_release_exp (btor, exp7);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_inc_exp_rww (void)
{
  FILE *fout     = fopen ("log/inc_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 8, "v1");
  BtorNode *exp2 = btor_inc_exp (btor, exp1);
  BtorNode *exp3 = btor_inc_exp (btor, exp1);
  assert (exp2 == exp3);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp3);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_delete_btor (btor);
  fclose (fout);
}

static void
test_dec_exp_rww (void)
{
  FILE *fout     = fopen ("log/dec_exp_rww.log", "w");
  Btor *btor     = btor_new_btor ();
  BtorNode *exp1 = btor_var_exp (btor, 8, "v1");
  BtorNode *exp2 = btor_dec_exp (btor, exp1);
  BtorNode *exp3 = btor_dec_exp (btor, exp1);
  assert (exp2 == exp3);
  btor->rewrite_writes = 1;
  btor_dump_exp (btor, fout, exp3);
  btor_release_exp (btor, exp1);
  btor_release_exp (btor, exp2);
  btor_release_exp (btor, exp3);
  btor_delete_btor (btor);
  fclose (fout);
}

void
run_exp_rww_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_btor);
  BTOR_RUN_TEST_CHECK_LOG (const_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (zero_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (ones_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (one_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (unsigned_to_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (var_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (array_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (not_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (neg_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (redor_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (redxor_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (redand_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (slice_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (uext_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (sext_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (or_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (xor_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (xnor_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (and_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (eq_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (ne_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (add_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (uaddo_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (saddo_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (mul_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (ult_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (slt_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (ulte_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (slte_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (ugt_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (sgt_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (ugte_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (sgte_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (umulo_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (smulo_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (sll_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (srl_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (sra_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (rol_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (ror_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (sub_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (usubo_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (ssubo_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (udiv_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (sdiv_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (sdivo_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (urem_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (srem_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (smod_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (concat_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (read_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (cond_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (write_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (inc_exp_rww);
  BTOR_RUN_TEST_CHECK_LOG (dec_exp_rww);
}

void
finish_exp_rww_tests (void)
{
}

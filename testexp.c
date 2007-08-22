#include "testexp.h"
#include "btorexp.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

void
init_exp_tests (void)
{
}

static void
test_new_delete_exp_mgr (void)
{
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  btor_delete_exp_mgr (emgr);
}

static void
test_const_exp (void)
{
  FILE *fout       = fopen ("log/const_exp.log", "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_const_exp (emgr, "00010011");
  BtorExp *exp2    = btor_const_exp (emgr, "00010011");
  BtorExp *exp3    = btor_const_exp (emgr, "0000000000010011");
  assert (exp1 == exp2);
  assert (exp2 != exp3);
  assert (btor_get_exp_len (emgr, exp1) == 8);
  assert (btor_get_exp_len (emgr, exp2) == 8);
  assert (btor_get_exp_len (emgr, exp3) == 16);
  btor_dump_exp (emgr, fout, exp2);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_var_exp (void)
{
  FILE *fout       = fopen ("log/var_exp.log", "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 8, "v1");
  BtorExp *exp2    = btor_copy_exp (emgr, exp1);
  assert (exp1 == exp2);
  assert (btor_get_exp_len (emgr, exp1) == 8);
  assert (btor_get_exp_len (emgr, exp2) == 8);
  btor_dump_exp (emgr, fout, exp2);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_array_exp (void)
{
  FILE *fout       = fopen ("log/array_exp.log", "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_array_exp (emgr, 32, 8, "a1");
  BtorExp *exp2    = btor_copy_exp (emgr, exp1);
  BtorExp *exp3    = btor_array_exp (emgr, 32, 8, "a2");
  assert (exp1 == exp2);
  assert (exp1 != exp3);
  assert (btor_get_exp_len (emgr, exp1) == 32);
  assert (btor_get_exp_len (emgr, exp2) == 32);
  assert (btor_get_exp_len (emgr, exp3) == 32);
  assert (btor_get_index_exp_len (emgr, exp1) == 8);
  assert (btor_get_index_exp_len (emgr, exp2) == 8);
  assert (btor_get_index_exp_len (emgr, exp3) == 8);
  btor_dump_exp (emgr, fout, exp2);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
unary_exp_test (BtorExp *(*func) (BtorExpMgr *, BtorExp *), char *log)
{
  FILE *fout       = fopen (log, "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 8, "v1");
  BtorExp *exp2    = func (emgr, exp1);
  BtorExp *exp3    = func (emgr, exp1);
  assert (exp2 == exp3);
  assert (btor_get_exp_len (emgr, exp1) == 8);
  if (func == btor_not_exp || func == btor_neg_exp)
  {
    assert (btor_get_exp_len (emgr, exp2) == 8);
    assert (btor_get_exp_len (emgr, exp3) == 8);
  }
  else
  {
    assert (btor_get_exp_len (emgr, exp2) == 1);
    assert (btor_get_exp_len (emgr, exp3) == 1);
  }
  btor_dump_exp (emgr, fout, exp3);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_not_exp (void)
{
  unary_exp_test (btor_not_exp, "log/not_exp.log");
}

static void
test_neg_exp (void)
{
  unary_exp_test (btor_neg_exp, "log/neg_exp.log");
}

static void
test_nego_exp (void)
{
  unary_exp_test (btor_nego_exp, "log/nego_exp.log");
}

static void
test_redor_exp (void)
{
  unary_exp_test (btor_redor_exp, "log/redor_exp.log");
}

static void
test_redxor_exp (void)
{
  unary_exp_test (btor_redxor_exp, "log/redxor_exp.log");
}

static void
test_redand_exp (void)
{
  unary_exp_test (btor_redand_exp, "log/redand_exp.log");
}

static void
test_slice_exp (void)
{
  FILE *fout       = fopen ("log/slice_exp.log", "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 32, "v1");
  BtorExp *exp2    = btor_slice_exp (emgr, exp1, 31, 30);
  BtorExp *exp3    = btor_slice_exp (emgr, exp1, 31, 30);
  assert (exp2 == exp3);
  btor_dump_exp (emgr, fout, exp3);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
ext_exp_test (BtorExp *(*func) (BtorExpMgr *, BtorExp *, int), char *log)
{
  FILE *fout       = fopen (log, "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 32, "v1");
  BtorExp *exp2    = func (emgr, exp1, 32);
  BtorExp *exp3    = func (emgr, exp1, 32);
  assert (exp2 == exp3);
  btor_dump_exp (emgr, fout, exp3);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_uext_exp (void)
{
  ext_exp_test (btor_uext_exp, "log/uext_exp.log");
}

static void
test_sext_exp (void)
{
  ext_exp_test (btor_sext_exp, "log/sext_exp.log");
}

static void
binary_commutative_exp_test (
    BtorExp *(*func) (BtorExpMgr *, BtorExp *, BtorExp *), char *log)
{
  FILE *fout       = fopen (log, "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 8, "v1");
  BtorExp *exp2    = btor_var_exp (emgr, 8, "v2");
  BtorExp *exp3    = func (emgr, exp1, exp2);
  BtorExp *exp4    = func (emgr, exp1, exp2);
  BtorExp *exp5    = func (emgr, exp2, exp1);
  assert (exp3 == exp4);
  assert (exp4 == exp5);
  assert (btor_get_exp_len (emgr, exp1) == 8);
  assert (btor_get_exp_len (emgr, exp2) == 8);
  if (func == btor_eq_exp || func == btor_ne_exp || func == btor_uaddo_exp
      || func == btor_saddo_exp || func == btor_umulo_exp)
  {
    assert (btor_get_exp_len (emgr, exp3) == 1);
    assert (btor_get_exp_len (emgr, exp4) == 1);
    assert (btor_get_exp_len (emgr, exp5) == 1);
  }
  else
  {
    assert (btor_get_exp_len (emgr, exp3) == 8);
    assert (btor_get_exp_len (emgr, exp4) == 8);
    assert (btor_get_exp_len (emgr, exp5) == 8);
  }
  btor_dump_exp (emgr, fout, exp3);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_release_exp (emgr, exp4);
  btor_release_exp (emgr, exp5);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_or_exp (void)
{
  binary_commutative_exp_test (btor_or_exp, "log/or_exp.log");
}

static void
test_xor_exp (void)
{
  binary_commutative_exp_test (btor_xor_exp, "log/xor_exp.log");
}

static void
test_xnor_exp (void)
{
  binary_commutative_exp_test (btor_xnor_exp, "log/xnor_exp.log");
}

static void
test_and_exp (void)
{
  binary_commutative_exp_test (btor_and_exp, "log/and_exp.log");
}

static void
test_eq_exp (void)
{
  binary_commutative_exp_test (btor_eq_exp, "log/eq_exp.log");
}

static void
test_ne_exp (void)
{
  binary_commutative_exp_test (btor_ne_exp, "log/ne_exp.log");
}

static void
test_add_exp (void)
{
  binary_commutative_exp_test (btor_add_exp, "log/add_exp.log");
}

static void
test_uaddo_exp (void)
{
  binary_commutative_exp_test (btor_uaddo_exp, "log/uaddo_exp.log");
}

static void
test_saddo_exp (void)
{
  binary_commutative_exp_test (btor_saddo_exp, "log/saddo_exp.log");
}

static void
test_umul_exp (void)
{
  binary_commutative_exp_test (btor_umul_exp, "log/umul_exp.log");
}

static void
test_smul_exp (void)
{
  binary_commutative_exp_test (btor_smul_exp, "log/smul_exp.log");
}

static void
binary_non_commutative_exp_test (
    BtorExp *(*func) (BtorExpMgr *, BtorExp *, BtorExp *), char *log)
{
  FILE *fout       = fopen (log, "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 32, "v1");
  BtorExp *exp2    = btor_var_exp (emgr, 32, "v2");
  BtorExp *exp3    = func (emgr, exp1, exp2);
  BtorExp *exp4    = func (emgr, exp1, exp2);
  BtorExp *exp5    = func (emgr, exp2, exp1);
  assert (exp3 == exp4);
  assert (exp4 != exp5);
  if (func == btor_sub_exp || func == btor_udiv_exp || func == btor_sdiv_exp
      || func == btor_umod_exp || func == btor_smod_exp)
  {
    assert (btor_get_exp_len (emgr, exp3) == 32);
    assert (btor_get_exp_len (emgr, exp4) == 32);
    assert (btor_get_exp_len (emgr, exp5) == 32);
  }
  else if (func == btor_concat_exp)
  {
    assert (btor_get_exp_len (emgr, exp3) == 64);
    assert (btor_get_exp_len (emgr, exp4) == 64);
    assert (btor_get_exp_len (emgr, exp5) == 64);
  }
  else
  {
    assert (btor_get_exp_len (emgr, exp3) == 1);
    assert (btor_get_exp_len (emgr, exp4) == 1);
    assert (btor_get_exp_len (emgr, exp5) == 1);
  }
  btor_dump_exp (emgr, fout, exp4);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_release_exp (emgr, exp4);
  btor_release_exp (emgr, exp5);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_ult_exp (void)
{
  binary_non_commutative_exp_test (btor_ult_exp, "log/ult_exp.log");
}

static void
test_slt_exp (void)
{
  binary_non_commutative_exp_test (btor_slt_exp, "log/slt_exp.log");
}

static void
test_ulte_exp (void)
{
  binary_non_commutative_exp_test (btor_ulte_exp, "log/ulte_exp.log");
}

static void
test_slte_exp (void)
{
  binary_non_commutative_exp_test (btor_slte_exp, "log/slte_exp.log");
}

static void
test_ugt_exp (void)
{
  binary_non_commutative_exp_test (btor_ugt_exp, "log/ugt_exp.log");
}

static void
test_sgt_exp (void)
{
  binary_non_commutative_exp_test (btor_sgt_exp, "log/sgt_exp.log");
}

static void
test_ugte_exp (void)
{
  binary_non_commutative_exp_test (btor_ugte_exp, "log/ugte_exp.log");
}

static void
test_sgte_exp (void)
{
  binary_non_commutative_exp_test (btor_sgte_exp, "log/sgte_exp.log");
}

static void
test_sub_exp (void)
{
  binary_non_commutative_exp_test (btor_sub_exp, "log/sub_exp.log");
}

static void
test_usubo_exp (void)
{
  binary_non_commutative_exp_test (btor_usubo_exp, "log/usubo_exp.log");
}

static void
test_ssubo_exp (void)
{
  binary_non_commutative_exp_test (btor_ssubo_exp, "log/ssubo_exp.log");
}

static void
test_udiv_exp (void)
{
  binary_non_commutative_exp_test (btor_udiv_exp, "log/udiv_exp.log");
}

static void
test_sdiv_exp (void)
{
  binary_non_commutative_exp_test (btor_sdiv_exp, "log/sdiv_exp.log");
}

static void
test_sdivo_exp (void)
{
  binary_non_commutative_exp_test (btor_sdivo_exp, "log/sdivo_exp.log");
}

static void
test_umod_exp (void)
{
  binary_non_commutative_exp_test (btor_umod_exp, "log/umod_exp.log");
}

static void
test_smod_exp (void)
{
  binary_non_commutative_exp_test (btor_smod_exp, "log/smod_exp.log");
}

static void
test_concat_exp (void)
{
  binary_non_commutative_exp_test (btor_concat_exp, "log/concat_exp.log");
}

static void
mulo_exp_test (BtorExp *(*func) (BtorExpMgr *, BtorExp *, BtorExp *), char *log)
{
  FILE *fout       = fopen (log, "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 3, "v1");
  BtorExp *exp2    = btor_var_exp (emgr, 3, "v2");
  BtorExp *exp3    = func (emgr, exp1, exp2);
  BtorExp *exp4    = func (emgr, exp1, exp2);
  BtorExp *exp5    = func (emgr, exp2, exp1);
  assert (exp3 == exp4);
  if (func == btor_umulo_exp)
    assert (exp4 != exp5);
  else
    assert (exp4 == exp5);
  assert (btor_get_exp_len (emgr, exp3) == 1);
  assert (btor_get_exp_len (emgr, exp4) == 1);
  assert (btor_get_exp_len (emgr, exp5) == 1);
  btor_dump_exp (emgr, fout, exp4);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_release_exp (emgr, exp4);
  btor_release_exp (emgr, exp5);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_umulo_exp (void)
{
  /* Implementation is not symmetric */
  mulo_exp_test (btor_umulo_exp, "log/umulo_exp.log");
}

static void
test_smulo_exp (void)
{
  mulo_exp_test (btor_smulo_exp, "log/smulo_exp.log");
}

static void
shift_exp_test (BtorExp *(*func) (BtorExpMgr *, BtorExp *, BtorExp *),
                char *log)
{
  FILE *fout       = fopen (log, "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 32, "v1");
  BtorExp *exp2    = btor_var_exp (emgr, 5, "v2");
  BtorExp *exp3    = func (emgr, exp1, exp2);
  BtorExp *exp4    = func (emgr, exp1, exp2);
  assert (exp3 == exp4);
  assert (btor_get_exp_len (emgr, exp1) == 32);
  assert (btor_get_exp_len (emgr, exp2) == 5);
  assert (btor_get_exp_len (emgr, exp3) == 32);
  assert (btor_get_exp_len (emgr, exp4) == 32);
  btor_dump_exp (emgr, fout, exp4);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_release_exp (emgr, exp4);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_sll_exp (void)
{
  shift_exp_test (btor_sll_exp, "log/sll_exp.log");
}

static void
test_srl_exp (void)
{
  shift_exp_test (btor_srl_exp, "log/srl_exp.log");
}

static void
test_sra_exp (void)
{
  shift_exp_test (btor_sra_exp, "log/sra_exp.log");
}

static void
test_rol_exp (void)
{
  shift_exp_test (btor_rol_exp, "log/rol_exp.log");
}

static void
test_ror_exp (void)
{
  shift_exp_test (btor_ror_exp, "log/ror_exp.log");
}

static void
test_acc_exp (void)
{
  FILE *fout       = fopen ("log/acc_exp.log", "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_array_exp (emgr, 32, 8, "a1");
  BtorExp *exp2    = btor_var_exp (emgr, 8, "v1");
  BtorExp *exp3    = btor_acc_exp (emgr, exp1, exp2);
  BtorExp *exp4    = btor_acc_exp (emgr, exp1, exp2);
  assert (exp4 == exp3);
  assert (btor_get_exp_len (emgr, exp1) == 32);
  assert (btor_get_index_exp_len (emgr, exp1) == 8);
  assert (btor_get_exp_len (emgr, exp2) == 8);
  assert (btor_get_exp_len (emgr, exp3) == 32);
  assert (btor_get_exp_len (emgr, exp4) == 32);
  btor_dump_exp (emgr, fout, exp4);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_release_exp (emgr, exp4);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_cond_exp (void)
{
  FILE *fout       = fopen ("log/cond_exp.log", "w");
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 1, "v1");
  BtorExp *exp2    = btor_var_exp (emgr, 32, "v2");
  BtorExp *exp3    = btor_const_exp (emgr, "00110111001101010001010100110100");
  BtorExp *exp4    = btor_cond_exp (emgr, exp1, exp2, exp3);
  BtorExp *exp5    = btor_cond_exp (emgr, exp1, exp2, exp3);
  BtorExp *exp6    = btor_cond_exp (emgr, exp1, exp3, exp2);
  assert (exp4 == exp5);
  assert (exp4 != exp6);
  assert (btor_get_exp_len (emgr, exp1) == 1);
  assert (btor_get_exp_len (emgr, exp2) == 32);
  assert (btor_get_exp_len (emgr, exp3) == 32);
  assert (btor_get_exp_len (emgr, exp4) == 32);
  assert (btor_get_exp_len (emgr, exp5) == 32);
  assert (btor_get_exp_len (emgr, exp6) == 32);
  btor_dump_exp (emgr, fout, exp4);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_release_exp (emgr, exp4);
  btor_release_exp (emgr, exp5);
  btor_release_exp (emgr, exp6);
  btor_delete_exp_mgr (emgr);
  fclose (fout);
}

static void
test_exp_to_aig (void)
{
  BtorExpMgr *emgr = btor_new_exp_mgr (0, 0, 0, stdout);
  BtorExp *exp1    = btor_var_exp (emgr, 1, "v1");
  BtorExp *exp2    = btor_var_exp (emgr, 32, "v2");
  BtorExp *exp3    = btor_var_exp (emgr, 32, "v3");
  BtorExp *exp4    = btor_cond_exp (emgr, exp1, exp2, exp3);
  BtorExp *exp5    = btor_var_exp (emgr, 32, "v4");
  BtorExp *exp6    = btor_and_exp (emgr, exp4, exp5);
  BtorExp *exp7    = btor_slice_exp (emgr, exp6, 31, 31);
  BtorAIG *result  = btor_exp_to_aig (emgr, exp7);
  btor_release_aig (
      btor_get_aig_mgr_aigvec_mgr (btor_get_aigvec_mgr_exp_mgr (emgr)), result);
  btor_release_exp (emgr, exp1);
  btor_release_exp (emgr, exp2);
  btor_release_exp (emgr, exp3);
  btor_release_exp (emgr, exp4);
  btor_release_exp (emgr, exp5);
  btor_release_exp (emgr, exp6);
  btor_release_exp (emgr, exp7);
  btor_delete_exp_mgr (emgr);
}

void
run_exp_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_exp_mgr);
  BTOR_RUN_TEST_CHECK_LOG (const_exp);
  BTOR_RUN_TEST_CHECK_LOG (var_exp);
  BTOR_RUN_TEST_CHECK_LOG (array_exp);
  BTOR_RUN_TEST_CHECK_LOG (not_exp);
  BTOR_RUN_TEST_CHECK_LOG (neg_exp);
  BTOR_RUN_TEST_CHECK_LOG (nego_exp);
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
  BTOR_RUN_TEST_CHECK_LOG (umul_exp);
  BTOR_RUN_TEST_CHECK_LOG (smul_exp);
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
  BTOR_RUN_TEST_CHECK_LOG (umod_exp);
  BTOR_RUN_TEST_CHECK_LOG (smod_exp);
  BTOR_RUN_TEST_CHECK_LOG (concat_exp);
  BTOR_RUN_TEST_CHECK_LOG (acc_exp);
  BTOR_RUN_TEST_CHECK_LOG (cond_exp);
  BTOR_RUN_TEST (exp_to_aig);
}

void
finish_exp_tests (void)
{
}

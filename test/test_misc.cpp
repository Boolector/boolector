/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolector.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"
}

class TestMisc : public TestMm
{
 protected:
  static constexpr uint32_t BTOR_TEST_MISC_LOW  = 1;
  static constexpr uint32_t BTOR_TEST_MISC_HIGH = 4;
  static constexpr uint32_t UEXT                = 0;
  static constexpr uint32_t SEXT                = 1;

  char *int_to_str (int32_t x, int32_t num_bits)
  {
    assert (x >= 0);
    assert (num_bits > 0);
    char *result = nullptr;
    int32_t i    = 0;
    result = (char *) btor_mem_malloc (d_mm, sizeof (char) * (num_bits + 1));
    for (i = num_bits - 1; i >= 0; i--)
    {
      result[i] = x % 2 ? '1' : '0';
      x >>= 1;
    }
    result[num_bits] = '\0';
    return result;
  }

  char *mk_slice (int32_t x, int32_t high, int32_t low, int32_t num_bits)
  {
    assert (high < num_bits);
    assert (low >= 0);
    assert (low <= high);
    char *temp      = nullptr;
    char *result    = nullptr;
    int32_t i       = 0;
    int32_t counter = 0;
    temp = int_to_str (x, num_bits);
    assert (temp != nullptr);
    result  = int_to_str (0, high - low + 1);
    counter = high - low;
    for (i = low; i <= high; i++) result[counter--] = temp[num_bits - 1 - i];
    btor_mem_freestr (d_mm, temp);
    return result;
  }

  void slice_test_misc (int32_t low, int32_t high, uint32_t rwl)
  {
    assert (low > 0);
    assert (low <= high);

    Btor *btor;
    int32_t i        = 0;
    int32_t j        = 0;
    char *result     = 0;
    int32_t num_bits = 0;
    const int32_t x  = 11;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      for (i = num_bits - 1; i >= 0; i--)
      {
        for (j = i; j >= 0; j--)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *slice, *eq;

          btor = boolector_new ();
          boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);

          result = mk_slice (x, i, j, num_bits);

          sort   = boolector_bitvec_sort (btor, high);
          const1 = boolector_unsigned_int (btor, x, sort);
          slice  = boolector_slice (btor, const1, i, j);
          const2 = boolector_const (btor, result);
          eq     = boolector_eq (btor, slice, const2);
          boolector_assert (btor, eq);

          ASSERT_EQ (boolector_sat (btor), BOOLECTOR_SAT);
          boolector_release_sort (btor, sort);
          boolector_release (btor, const1);
          boolector_release (btor, const2);
          boolector_release (btor, slice);
          boolector_release (btor, eq);
          boolector_delete (btor);
          btor_mem_freestr (d_mm, result);
        }
      }
    }
  }

  char *uext (int32_t x, int32_t y, int32_t num_bits)
  {
    assert (x >= 0);
    assert (y >= 0);
    assert (num_bits >= 1);
    char *result = nullptr;
    result = int_to_str (x, num_bits + y);
    return result;
  }

  char *sext (int32_t x, int32_t y, int32_t num_bits)
  {
    assert (x >= 0);
    assert (y >= 0);
    assert (num_bits >= 1);
    char *result = nullptr;
    int32_t i    = 0;
    result = int_to_str (x, num_bits + y);
    if (result[y] == '1')
    {
      for (i = 0; i < y; i++) result[i] = '1';
    }
    return result;
  }

  void ext_test_misc (uint32_t ext_mode,
                      int32_t low,
                      int32_t high,
                      uint32_t rwl)
  {
    assert (ext_mode == UEXT || ext_mode == SEXT);
    assert (low > 0);
    assert (low <= high);

    Btor *btor;
    BoolectorNode *(*btor_fun) (Btor *, BoolectorNode *, uint32_t);

    int32_t i        = 0;
    int32_t j        = 0;
    int32_t max      = 0;
    char *result     = 0;
    int32_t num_bits = 0;

    btor_fun = ext_mode == UEXT ? boolector_uext : boolector_sext;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < num_bits; j++)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *eq, *bfun;

          btor = boolector_new ();
          boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);

          result =
              ext_mode == UEXT ? uext (i, j, num_bits) : sext (i, j, num_bits);

          sort   = boolector_bitvec_sort (btor, num_bits);
          const1 = boolector_unsigned_int (btor, i, sort);
          bfun   = btor_fun (btor, const1, j);
          const2 = boolector_const (btor, result);
          eq     = boolector_eq (btor, bfun, const2);
          boolector_assert (btor, eq);

          ASSERT_EQ (boolector_sat (btor), BOOLECTOR_SAT);
          boolector_release_sort (btor, sort);
          boolector_release (btor, const1);
          boolector_release (btor, const2);
          boolector_release (btor, bfun);
          boolector_release (btor, eq);
          boolector_delete (btor);
          btor_mem_freestr (d_mm, result);
        }
      }
    }
  }

  char *mk_concat (int32_t x, int32_t y, int32_t num_bits)
  {
    assert (x >= 0);
    assert (y >= 0);
    assert (num_bits > 0);
    assert (num_bits <= INT32_MAX / 2);

    char *x_string = nullptr;
    char *y_string = nullptr;
    char *result   = nullptr;

    x_string = int_to_str (x, num_bits);
    y_string = int_to_str (y, num_bits);
    result =
        (char *) btor_mem_malloc (d_mm, sizeof (char) * ((num_bits << 1) + 1));
    strcpy (result, x_string);
    strcat (result, y_string);
    btor_mem_freestr (d_mm, x_string);
    btor_mem_freestr (d_mm, y_string);
    return result;
  }

  void concat_test_misc (int32_t low, int32_t high, uint32_t rwl)
  {
    assert (low > 0);
    assert (low <= high);

    Btor *btor;
    int32_t i        = 0;
    int32_t j        = 0;
    int32_t max      = 0;
    char *result     = 0;
    int32_t num_bits = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *const3, *eq, *concat;

          btor = boolector_new ();
          boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);

          result = mk_concat (i, j, num_bits);

          sort   = boolector_bitvec_sort (btor, num_bits);
          const1 = boolector_unsigned_int (btor, i, sort);
          const2 = boolector_unsigned_int (btor, j, sort);
          concat = boolector_concat (btor, const1, const2);
          const3 = boolector_const (btor, result);
          eq     = boolector_eq (btor, concat, const3);
          boolector_assert (btor, eq);

          ASSERT_EQ (boolector_sat (btor), BOOLECTOR_SAT);
          boolector_release_sort (btor, sort);
          boolector_release (btor, const1);
          boolector_release (btor, const2);
          boolector_release (btor, const3);
          boolector_release (btor, concat);
          boolector_release (btor, eq);
          boolector_delete (btor);
          btor_mem_freestr (d_mm, result);
        }
      }
    }
  }

  static void cond_test_misc (int32_t low, int32_t high, uint32_t rwl)
  {
    assert (low > 0);
    assert (low <= high);

    Btor *btor;
    int32_t i        = 0;
    int32_t j        = 0;
    int32_t k        = 0;
    int32_t max      = 0;
    int32_t result   = 0;
    int32_t num_bits = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          for (k = 0; k <= 1; k++)
          {
            BoolectorSort sort, sort1;
            BoolectorNode *const1, *const2, *const3, *const4, *eq, *cond;

            btor = boolector_new ();
            boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);

            result = k ? i : j;

            sort   = boolector_bitvec_sort (btor, num_bits);
            sort1  = boolector_bitvec_sort (btor, 1);
            const1 = boolector_unsigned_int (btor, i, sort);
            const2 = boolector_unsigned_int (btor, j, sort);
            const3 = boolector_unsigned_int (btor, k, sort1);
            cond   = boolector_cond (btor, const3, const1, const2);
            const4 = boolector_unsigned_int (btor, result, sort);
            eq     = boolector_eq (btor, cond, const4);
            boolector_assert (btor, eq);

            ASSERT_EQ (boolector_sat (btor), BOOLECTOR_SAT);
            boolector_release_sort (btor, sort);
            boolector_release_sort (btor, sort1);
            boolector_release (btor, const1);
            boolector_release (btor, const2);
            boolector_release (btor, const3);
            boolector_release (btor, const4);
            boolector_release (btor, cond);
            boolector_release (btor, eq);
            boolector_delete (btor);
          }
        }
      }
    }
  }

  void read_test_misc (int32_t low, int32_t high, uint32_t rwl)
  {
    assert (low > 0);
    assert (low <= high);

    Btor *btor;
    int32_t i        = 0;
    int32_t j        = 0;
    int32_t max      = 0;
    int32_t num_bits = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          BoolectorSort elem_sort, index_sort, array_sort;
          BoolectorNode *const1, *const2, *const3, *const4;
          BoolectorNode *eq1, *eq2, *array, *read1, *read2;

          btor = boolector_new ();
          boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);

          elem_sort  = boolector_bitvec_sort (btor, num_bits);
          index_sort = boolector_bitvec_sort (btor, 1);
          array_sort = boolector_array_sort (btor, index_sort, elem_sort);
          array      = boolector_array (btor, array_sort, "array");
          const1     = boolector_false (btor);
          const2     = boolector_true (btor);
          const3     = boolector_unsigned_int (btor, i, elem_sort);
          const4     = boolector_unsigned_int (btor, j, elem_sort);
          read1      = boolector_read (btor, array, const1);
          read2      = boolector_read (btor, array, const2);
          eq1        = boolector_eq (btor, const3, read1);
          eq2        = boolector_eq (btor, const4, read2);
          boolector_assert (btor, eq1);
          boolector_assert (btor, eq2);

          ASSERT_EQ (boolector_sat (btor), BOOLECTOR_SAT);
          boolector_release_sort (btor, elem_sort);
          boolector_release_sort (btor, index_sort);
          boolector_release_sort (btor, array_sort);
          boolector_release (btor, eq1);
          boolector_release (btor, eq2);
          boolector_release (btor, read1);
          boolector_release (btor, read2);
          boolector_release (btor, const1);
          boolector_release (btor, const2);
          boolector_release (btor, const3);
          boolector_release (btor, const4);
          boolector_release (btor, array);
          boolector_delete (btor);
        }
      }
    }
  }
};

TEST_F (TestMisc, slice)
{
  slice_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  slice_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

TEST_F (TestMisc, uext)
{
  ext_test_misc (UEXT, BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  ext_test_misc (UEXT, BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

TEST_F (TestMisc, sext)
{
  ext_test_misc (SEXT, BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  ext_test_misc (SEXT, BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

TEST_F (TestMisc, concat)
{
  concat_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  concat_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

TEST_F (TestMisc, cond)
{
  cond_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  cond_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

TEST_F (TestMisc, read)
{
  read_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  read_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

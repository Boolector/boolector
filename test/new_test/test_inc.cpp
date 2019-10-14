/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz
 *  Copyright (C) 2016 Mathias Preiner
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "btoropt.h"
}

class TestInc : public TestBoolector
{
 protected:
  void test_inc_counter (uint32_t w, bool nondet)
  {
    assert (w > 0);

    BoolectorNode *nonzero, *allzero, *one, *oracle;
    BoolectorNode *current, *next, *inc;
    BoolectorSort s;
    char name[100];
    uint32_t i;
    int32_t res;

    boolector_set_opt (btor, BTOR_OPT_INCREMENTAL, 1);
    s       = boolector_bitvec_sort (btor, w);
    one     = boolector_one (btor, s);
    current = boolector_zero (btor, s);
    boolector_release_sort (btor, s);
    i = 0;

    for (;;)
    {
      inc = boolector_add (btor, current, one);

      if (nondet)
      {
        sprintf (name, "oracle%d", i);
        if (i)
        {
          s      = boolector_bool_sort (btor);
          oracle = boolector_var (btor, s, name);
          boolector_release_sort (btor, s);
        }

        else
          oracle = boolector_true (btor);
        next = boolector_cond (btor, oracle, inc, current);
        boolector_release (btor, oracle);
      }
      else
        next = boolector_copy (btor, inc);

      boolector_release (btor, inc);
      boolector_release (btor, current);
      current = next;

      nonzero = boolector_redor (btor, current);
      allzero = boolector_not (btor, nonzero);
      boolector_release (btor, nonzero);

      i++;

      boolector_assume (btor, allzero);

      res = boolector_sat (btor);
      if (res == BOOLECTOR_SAT)
      {
        boolector_release (btor, allzero);
        break;
      }
      ASSERT_EQ (res, BOOLECTOR_UNSAT);
      ASSERT_TRUE (boolector_failed (btor, allzero));
      ASSERT_LT (i, (uint32_t) (1 << w));
      boolector_release (btor, allzero);
    }

    ASSERT_EQ (i, (uint32_t) (1 << w));

    boolector_release (btor, one);
    boolector_release (btor, current);
  }

  void test_inc_lt (uint32_t w)
  {
    assert (w > 0);

    BoolectorNode *prev, *next, *lt;
    BoolectorSort s;
    char name[100];
    uint32_t i;
    int32_t res;

    boolector_set_opt (btor, BTOR_OPT_INCREMENTAL, 1);

    i    = 0;
    prev = 0;
    for (;;)
    {
      i++;

      sprintf (name, "%d", i);
      s    = boolector_bitvec_sort (btor, w);
      next = boolector_var (btor, s, name);
      boolector_release_sort (btor, s);

      if (prev)
      {
        lt = boolector_ult (btor, prev, next);
        boolector_assert (btor, lt);
        boolector_release (btor, lt);
        boolector_release (btor, prev);
      }

      prev = next;

      res = boolector_sat (btor);
      if (res == BOOLECTOR_UNSAT) break;

      ASSERT_EQ (res, BOOLECTOR_SAT);
      ASSERT_LE (i, (uint32_t) (1 << w));
    }

    ASSERT_EQ (i, (uint32_t) (1 << w) + 1);

    boolector_release (btor, prev);
  }
};

TEST_F (TestInc, true_false)
{
  BoolectorNode *ff;
  BoolectorNode *tt;
  int32_t res;

  ff = boolector_false (btor);
  tt = boolector_true (btor);
  boolector_set_opt (btor, BTOR_OPT_INCREMENTAL, 1);
  boolector_assume (btor, tt);
  res = boolector_sat (btor);
  ASSERT_EQ (res, BOOLECTOR_SAT);

  boolector_assume (btor, ff);
  res = boolector_sat (btor);
  ASSERT_EQ (res, BOOLECTOR_UNSAT);
  ASSERT_TRUE (boolector_failed (btor, ff));

  boolector_release (btor, ff);
  boolector_release (btor, tt);
}

TEST_F (TestInc, count1) { test_inc_counter (1, false); }

TEST_F (TestInc, count2) { test_inc_counter (2, false); }

TEST_F (TestInc, count3) { test_inc_counter (3, false); }

TEST_F (TestInc, count4) { test_inc_counter (4, false); }

TEST_F (TestInc, count8) { test_inc_counter (8, false); }

TEST_F (TestInc, count1nondet) { test_inc_counter (1, true); }

TEST_F (TestInc, count2nondet) { test_inc_counter (2, true); }

TEST_F (TestInc, count3nondet) { test_inc_counter (3, true); }

TEST_F (TestInc, count4nondet) { test_inc_counter (4, true); }

TEST_F (TestInc, count8nondet) { test_inc_counter (8, true); }

TEST_F (TestInc, lt1) { test_inc_lt (1); }

TEST_F (TestInc, lt2) { test_inc_lt (2); }

TEST_F (TestInc, lt3) { test_inc_lt (3); }

TEST_F (TestInc, lt4) { test_inc_lt (4); }

TEST_F (TestInc, lt8) { test_inc_lt (8); }

TEST_F (TestInc, assume_assert1)
{
  int32_t sat_result;
  BoolectorNode *array, *index1, *index2, *read1, *read2, *eq_index, *ne_read;
  BoolectorSort s, as;

  boolector_set_opt (btor, BTOR_OPT_INCREMENTAL, 1);
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
  s        = boolector_bool_sort (btor);
  as       = boolector_array_sort (btor, s, s);
  array    = boolector_array (btor, as, "array1");
  index1   = boolector_var (btor, s, "index1");
  index2   = boolector_var (btor, s, "index2");
  read1    = boolector_read (btor, array, index1);
  read2    = boolector_read (btor, array, index2);
  eq_index = boolector_eq (btor, index1, index2);
  ne_read  = boolector_ne (btor, read1, read2);
  boolector_assert (btor, ne_read);
  sat_result = boolector_sat (btor);
  ASSERT_EQ (sat_result, BOOLECTOR_SAT);
  boolector_assume (btor, eq_index);
  sat_result = boolector_sat (btor);
  ASSERT_EQ (sat_result, BOOLECTOR_UNSAT);
  ASSERT_TRUE (boolector_failed (btor, eq_index));
  sat_result = boolector_sat (btor);
  ASSERT_EQ (sat_result, BOOLECTOR_SAT);
  boolector_release (btor, array);
  boolector_release (btor, index1);
  boolector_release (btor, index2);
  boolector_release (btor, read1);
  boolector_release (btor, read2);
  boolector_release (btor, eq_index);
  boolector_release (btor, ne_read);
  boolector_release_sort (btor, s);
  boolector_release_sort (btor, as);
}

TEST_F (TestInc, lemmas_on_demand1)
{
  int32_t sat_result;
  BoolectorNode *array, *index1, *index2, *read1, *read2, *eq, *ne;
  BoolectorSort s, as;

  boolector_set_opt (btor, BTOR_OPT_INCREMENTAL, 1);
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
  s      = boolector_bool_sort (btor);
  as     = boolector_array_sort (btor, s, s);
  array  = boolector_array (btor, as, "array1");
  index1 = boolector_var (btor, s, "index1");
  index2 = boolector_var (btor, s, "index2");
  read1  = boolector_read (btor, array, index1);
  read2  = boolector_read (btor, array, index2);
  eq     = boolector_eq (btor, index1, index2);
  ne     = boolector_ne (btor, read1, read2);
  boolector_assert (btor, eq);
  boolector_assume (btor, ne);
  sat_result = boolector_sat (btor);
  ASSERT_EQ (sat_result, BOOLECTOR_UNSAT);
  ASSERT_TRUE (boolector_failed (btor, ne));
  sat_result = boolector_sat (btor);
  ASSERT_EQ (sat_result, BOOLECTOR_SAT);
  boolector_release (btor, array);
  boolector_release (btor, index1);
  boolector_release (btor, index2);
  boolector_release (btor, read1);
  boolector_release (btor, read2);
  boolector_release (btor, eq);
  boolector_release (btor, ne);
  boolector_release_sort (btor, s);
  boolector_release_sort (btor, as);
}

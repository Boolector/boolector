/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2016 Armin Biere.
 *  Copyright (C) 2016-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolectormc.h"
}

class TestMc : public TestMm
{
 protected:
  void SetUp () override
  {
    TestMm::SetUp ();
    d_check_log_file = false;
    d_mc             = boolector_mc_new ();
    d_btor           = boolector_mc_get_btor (d_mc);
  }

  void TearDown () override
  {
    tear_down_iteration ();
    TestMm::TearDown ();
  }

  void set_up_iteration ()
  {
    if (d_mc) boolector_mc_delete (d_mc);
    d_mc   = boolector_mc_new ();
    d_btor = boolector_mc_get_btor (d_mc);
  }

  void tear_down_iteration ()
  {
    if (d_mc) boolector_mc_delete (d_mc);
    d_mc   = nullptr;
    d_btor = nullptr;
  }

  void test_mc_print (BoolectorNode *node,
                      const char *name,
                      int32_t time,
                      FILE *file)
  {
    char *val = boolector_mc_assignment (d_mc, node, time);
    assert (val);
    fprintf (file, "%s = %s\n", name, val);
    fflush (file);
    boolector_mc_free_assignment (d_mc, val);
  }

  BtorMC *d_mc = nullptr;
  Btor *d_btor = nullptr;
};

/*------------------------------------------------------------------------*/

TEST_F (TestMc, new_delete) {}

/*------------------------------------------------------------------------*/

TEST_F (TestMc, toggle)
{
  open_log_file ("mctoggle");

  int32_t i, k, mode;
  BoolectorNode *bit, *one, *zero, *add, *bad;
  BoolectorSort s;

  for (mode = 0; mode < 2; mode++)
  {
    set_up_iteration ();

    s = boolector_bitvec_sort (d_btor, 1);
    if (mode) boolector_mc_set_opt (d_mc, BTOR_MC_OPT_TRACE_GEN, 1);

    // boolector_mc_set_opt (d_mc, BTOR_MC_OPT_VERBOSITY, 3);

    bit  = boolector_mc_state (d_mc, s, "counter");
    one  = boolector_one (d_btor, s);
    zero = boolector_zero (d_btor, s);
    add  = boolector_add (d_btor, bit, one);
    bad  = boolector_eq (d_btor, bit, one);

    boolector_mc_next (d_mc, bit, add);
    boolector_mc_init (d_mc, bit, zero);
    boolector_mc_bad (d_mc, bad);

    boolector_release (d_btor, one);
    boolector_release (d_btor, zero);
    boolector_release (d_btor, add);
    boolector_release (d_btor, bad);

    k = boolector_mc_bmc (d_mc, 0, 0);
    ASSERT_LT (k, 0);  // can not reach bad within k=0 steps

    k = boolector_mc_bmc (d_mc, 0, 1);
    ASSERT_TRUE (0 <= k && k <= 1);  // bad reached within k=1 steps

    if (mode)
    {
      fprintf (d_log_file, "Bad state property satisfied at k = %d:\n", k);
      for (i = 0; i <= k; i++)
      {
        fprintf (d_log_file, "\n");
        fprintf (d_log_file, "[ state at time %d ]\n", i);
        test_mc_print (bit, "bit", i, d_log_file);
      }
    }

    boolector_release (d_btor, bit);
    boolector_release_sort (d_btor, s);
  }
}

TEST_F (TestMc, count2enable)
{
  open_log_file ("mccount2enable");

  int32_t i, k, mode;
  BoolectorNode *counter;  // 2-bit state
  BoolectorNode *enable;   // one boolean control input
  BoolectorNode *one, *zero, *three, *add, *ifenable, *bad;
  BoolectorSort s1, s2;

  for (mode = 0; mode < 2; mode++)
  {
    set_up_iteration ();

    s1 = boolector_bitvec_sort (d_btor, 1);
    s2 = boolector_bitvec_sort (d_btor, 2);

    if (mode) boolector_mc_set_opt (d_mc, BTOR_MC_OPT_TRACE_GEN, 1);

    // boolector_mc_set_opt (d_mc, BTOR_MC_OPT_VERBOSITY, 3);

    counter = boolector_mc_state (d_mc, s2, "counter");
    enable  = boolector_mc_input (d_mc, s1, "enable");

    one      = boolector_one (d_btor, s2);
    zero     = boolector_zero (d_btor, s2);
    three    = boolector_const (d_btor, "11");
    add      = boolector_add (d_btor, counter, one);
    ifenable = boolector_cond (d_btor, enable, add, counter);
    bad      = boolector_eq (d_btor, counter, three);

    boolector_mc_next (d_mc, counter, ifenable);
    boolector_mc_init (d_mc, counter, zero);
    boolector_mc_bad (d_mc, bad);

    boolector_release (d_btor, one);
    boolector_release (d_btor, zero);
    boolector_release (d_btor, three);
    boolector_release (d_btor, add);
    boolector_release (d_btor, ifenable);
    boolector_release (d_btor, bad);

    k = boolector_mc_bmc (d_mc, 0, 1);
    ASSERT_LT (k, 0);  // can not reach bad within k=1 steps

    k = boolector_mc_bmc (d_mc, 0, 5);
    ASSERT_TRUE (0 <= k && k <= 5);  // bad reached within k=4 steps

    if (mode)
    {
      boolector_mc_dump (d_mc, d_log_file);
      fflush (d_log_file);
      fprintf (d_log_file, "Bad state property satisfied at k = %d:\n", k);
      for (i = 0; i <= k; i++)
      {
        fprintf (d_log_file, "\n");
        fprintf (d_log_file, "[ state at time %d ]\n", i);
        test_mc_print (counter, "counter", i, d_log_file);
        fprintf (d_log_file, "\n");
        fprintf (d_log_file, "[ input at time %d ]\n", i);
        test_mc_print (enable, "enable", i, d_log_file);
      }
    }

    boolector_release (d_btor, counter);
    boolector_release (d_btor, enable);
    boolector_release_sort (d_btor, s1);
    boolector_release_sort (d_btor, s2);
  }
}

TEST_F (TestMc, count2resetenable)
{
  open_log_file ("mccount2resetenable");

  int32_t k, i;
  BoolectorNode *one, *zero, *three, *add, *ifenable, *ifreset, *bad;
  BoolectorNode *counter;         // 2-bit state
  BoolectorNode *enable, *reset;  // two boolean control inputs
  BoolectorSort s1, s2;

  boolector_mc_set_opt (d_mc, BTOR_MC_OPT_TRACE_GEN, 1);
  // boolector_mc_set_opt (d_mc, BTOR_MC_OPT_VERBOSITY, 3);

  s1 = boolector_bitvec_sort (d_btor, 1);
  s2 = boolector_bitvec_sort (d_btor, 2);

  counter = boolector_mc_state (d_mc, s2, "counter");
  enable  = boolector_mc_input (d_mc, s1, "enable");
  reset   = boolector_mc_input (d_mc, s1, "reset");

  one  = boolector_one (d_btor, s2);
  zero = boolector_zero (d_btor, s2);
  boolector_release_sort (d_btor, s1);
  boolector_release_sort (d_btor, s2);
  three    = boolector_const (d_btor, "11");
  add      = boolector_add (d_btor, counter, one);
  ifenable = boolector_cond (d_btor, enable, add, counter);
  ifreset  = boolector_cond (d_btor, reset, ifenable, zero);
  bad      = boolector_eq (d_btor, counter, three);

  boolector_mc_next (d_mc, counter, ifreset);
  boolector_mc_init (d_mc, counter, zero);
  boolector_mc_bad (d_mc, bad);
  boolector_release (d_btor, one);
  boolector_release (d_btor, zero);
  boolector_release (d_btor, three);
  boolector_release (d_btor, add);
  boolector_release (d_btor, ifenable);
  boolector_release (d_btor, ifreset);
  boolector_release (d_btor, bad);

  k = boolector_mc_bmc (d_mc, 0, 2);
  ASSERT_LT (k, 0);  // can not reach bad within k=1 steps

  k = boolector_mc_bmc (d_mc, 0, 4);
  ASSERT_TRUE (0 <= k && k <= 4);  // bad reached within k=4 steps

  fprintf (d_log_file, "Bad state property satisfied at k = %d:\n", k);
  for (i = 0; i <= k; i++)
  {
    fprintf (d_log_file, "\n");
    fprintf (d_log_file, "[ state at time %d ]\n", i);
    test_mc_print (counter, "counter", i, d_log_file);
    fprintf (d_log_file, "[ input at time %d ]\n", i);
    test_mc_print (reset, "reset", i, d_log_file);
    test_mc_print (enable, "enable", i, d_log_file);
  }

  boolector_release (d_btor, counter);
  boolector_release (d_btor, enable);
  boolector_release (d_btor, reset);
}

#if 0
TEST_F (TestMc, twostepmodel)
{
  open_log_file ("mctwostepmodel");

  int32_t k, i;
  BoolectorNode * zero, * one;
  BoolectorNode * a, * b, * t, * n, * or, * xor;
  BoolectorNode * nexta, * nexta1, * nexta2;
  BoolectorNode * nextb, * nextb1, * nextb2;
  BoolectorNode * bad, * bada, *badb;
  BoolectorSort s;

  boolector_mc_set_opt (d_mc, BTOR_MC_OPT_TRACE_GEN, 1);
  boolector_mc_set_opt (d_mc, BTOR_MC_OPT_VERBOSITY, 3);

  s = boolector_bitvec_sort (d_btor, 1);
  a = boolector_mc_state (d_mc, s, "a");
  b = boolector_mc_state (d_mc, s, "b");

  or = boolector_or (d_btor, a, b);	// dangling ...
  xor = boolector_xor (d_btor, a, b);	// dangling ...

  one = boolector_ones (d_btor, s);
  zero = boolector_zero (d_btor, s);

  boolector_mc_init (d_mc, a, zero);
  boolector_mc_init (d_mc, b, zero);

  t = boolector_mc_input (d_mc, s, "t");
  n = boolector_not (d_btor, t);

  nexta1 = boolector_nor (d_btor, t, a);
  nexta2 = boolector_implies (d_btor, n, a);
  nexta = boolector_and (d_btor, nexta1, nexta2);

  nextb1 = boolector_nor (d_btor, n, b);
  nextb2 = boolector_implies (d_btor, t, b);
  nextb = boolector_and (d_btor, nextb1, nextb2);

  boolector_mc_next (d_mc, a, nexta);
  boolector_mc_next (d_mc, b, nextb);

  bada = boolector_eq (d_btor, a, one);
  badb = boolector_eq (d_btor, b, one);
  bad = boolector_and (d_btor, bada, badb);

  boolector_mc_bad (d_mc, bad);

  k = boolector_mc_bmc (d_mc, 0, 2);
  ASSERT_EQ (k, 2);			// can reach bad within k=2 steps

  fprintf (d_log_file, "Bad state property satisfied at k = %d:\n", k);
  for (i = 0; i <= k; i++)
    {
      fprintf (d_log_file, "\n");
      fprintf (d_log_file, "[ state at time %d ]\n", i);
      fprintf (d_log_file, "\n");
      test_mc_print(a, "a", i, d_log_file);
      test_mc_print(b, "b",i, d_log_file);
      fprintf (d_log_file, "\n");
      fprintf (d_log_file, "[ input at time %d ]\n", i);
      fprintf (d_log_file, "\n");
      test_mc_print(t, "t", i, d_log_file);
      test_mc_print(n, "n", i, d_log_file);
      fprintf (d_log_file, "\n");
      fprintf (d_log_file, "[ logic at time %d ]\n", i);
      fprintf (d_log_file, "\n");
      test_mc_print(nexta1, "nexta1", i, d_log_file);
      test_mc_print(nexta1, "nexta2", i, d_log_file);
      test_mc_print(nexta1, "nexta", i, d_log_file);
      test_mc_print(nexta1, "nextb1", i, d_log_file);
      test_mc_print(nexta1, "nextb2", i, d_log_file);
      test_mc_print(nexta1, "nextb", i, d_log_file);
      fprintf (d_log_file, "\n");
      fprintf (d_log_file, "[ dangling logic at time %d ]\n", i);
      fprintf (d_log_file, "\n");
      test_mc_print (or, "or", i, d_log_file);
      test_mc_print (xor, "xor", i, d_log_file);
      fprintf (d_log_file, "\n");
      fprintf (d_log_file, "[ output at time %d ]\n", i);
      fprintf (d_log_file, "\n");
      test_mc_print (bada, "bada", i, d_log_file);
      test_mc_print (badb, "badb", i, d_log_file);
      test_mc_print (bad, "bad", i, d_log_file);
    }

  boolector_release (d_btor, or);
  boolector_release (d_btor, xor);
  boolector_release (d_btor, one);
  boolector_release (d_btor, zero);
  boolector_release (d_btor, n);
  boolector_release (d_btor, nexta1);
  boolector_release (d_btor, nexta2);
  boolector_release (d_btor, nexta);
  boolector_release (d_btor, nextb1);
  boolector_release (d_btor, nextb2);
  boolector_release (d_btor, nextb);
  boolector_release (d_btor, bad);
  boolector_release (d_btor, bada);
  boolector_release (d_btor, badb);
  boolector_release_sort (d_btor, s);

  finish_mc_test ();
}
#endif

static int32_t test_mccount2multi_reached[4];

static void
test_mccount2multi_call_back (void *state, int32_t i, int32_t k)
{
  (void) state;
  assert (test_mccount2multi_reached == (int32_t *) state);
  assert (0 <= i), assert (i < 4);
  assert (k >= 0);
  assert (test_mccount2multi_reached[i] == -1);
  test_mccount2multi_reached[i] = k;
#if 0
  printf ("property %d reached at bound %d\n", i, k);
  fflush (stdout);
#endif
}

TEST_F (TestMc, count2multi)
{
  int32_t i, k;
  BoolectorSort s;

  // boolector_mc_set_opt (d_mc, BTOR_MC_OPT_VERBOSITY, 3);
  boolector_mc_set_opt (d_mc, BTOR_MC_OPT_STOP_FIRST, 0);

  BoolectorNode *count, *one, *zero, *two, *three, *next;
  BoolectorNode *eqzero, *eqone, *eqtwo, *eqthree;
  s     = boolector_bitvec_sort (d_btor, 2);
  count = boolector_mc_state (d_mc, s, "count");
  one   = boolector_one (d_btor, s);
  zero  = boolector_zero (d_btor, s);
  boolector_release_sort (d_btor, s);
  two   = boolector_const (d_btor, "10");
  three = boolector_const (d_btor, "11");
  next  = boolector_add (d_btor, count, one);
  boolector_mc_init (d_mc, count, zero);
  boolector_mc_next (d_mc, count, next);
  eqzero  = boolector_eq (d_btor, count, zero);
  eqone   = boolector_eq (d_btor, count, one);
  eqtwo   = boolector_eq (d_btor, count, two);
  eqthree = boolector_eq (d_btor, count, three);
  i       = boolector_mc_bad (d_mc, eqzero);
  ASSERT_EQ (i, 0);
  i = boolector_mc_bad (d_mc, eqone);
  ASSERT_EQ (i, 1);
  i = boolector_mc_bad (d_mc, eqtwo);
  ASSERT_EQ (i, 2);
  i = boolector_mc_bad (d_mc, eqthree);
  ASSERT_EQ (i, 3);
  boolector_release (d_btor, one);
  boolector_release (d_btor, zero);
  boolector_release (d_btor, two);
  boolector_release (d_btor, three);
  boolector_release (d_btor, eqone);
  boolector_release (d_btor, eqzero);
  boolector_release (d_btor, eqtwo);
  boolector_release (d_btor, eqthree);
  boolector_release (d_btor, next);

  test_mccount2multi_reached[0] = -1;
  test_mccount2multi_reached[1] = -1;
  test_mccount2multi_reached[2] = -1;
  test_mccount2multi_reached[3] = -1;
  boolector_mc_set_reached_at_bound_call_back (
      d_mc, test_mccount2multi_reached, test_mccount2multi_call_back);
  k = boolector_mc_bmc (d_mc, 2, 3);
  ASSERT_EQ (k, 3);
  ASSERT_EQ (test_mccount2multi_reached[0], -1);
  ASSERT_EQ (test_mccount2multi_reached[1], -1);
  ASSERT_EQ (test_mccount2multi_reached[2], 2);
  ASSERT_EQ (test_mccount2multi_reached[3], 3);
  ASSERT_LT (boolector_mc_reached_bad_at_bound (d_mc, 0), 0);
  ASSERT_LT (boolector_mc_reached_bad_at_bound (d_mc, 1), 0);
  ASSERT_EQ (boolector_mc_reached_bad_at_bound (d_mc, 2), 2);
  ASSERT_EQ (boolector_mc_reached_bad_at_bound (d_mc, 3), 3);
  k = boolector_mc_bmc (d_mc, 4, 10);
  ASSERT_EQ (k, 5);
  ASSERT_EQ (test_mccount2multi_reached[0], 4);
  ASSERT_EQ (test_mccount2multi_reached[1], 5);
  ASSERT_EQ (test_mccount2multi_reached[2], 2);
  ASSERT_EQ (test_mccount2multi_reached[3], 3);
  ASSERT_EQ (boolector_mc_reached_bad_at_bound (d_mc, 0), 4);
  ASSERT_EQ (boolector_mc_reached_bad_at_bound (d_mc, 1), 5);
  ASSERT_EQ (boolector_mc_reached_bad_at_bound (d_mc, 2), 2);
  ASSERT_EQ (boolector_mc_reached_bad_at_bound (d_mc, 3), 3);
  boolector_release (d_btor, count);
}

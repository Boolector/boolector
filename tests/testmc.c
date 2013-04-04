/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *
 *  All rights reserved.
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testmc.h"
#include "btormc.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static BtorMC *g_mc;
static Btor *g_btor;

void
init_mc_tests (void)
{
  assert (!g_mc);
  assert (!g_btor);
}

void
finish_mc_tests (void)
{
  assert (!g_mc);
  assert (!g_btor);
}

/*------------------------------------------------------------------------*/

static void
init_mc_test (void)
{
  assert (!g_mc);
  g_mc = boolector_new_mc ();
  assert (!g_btor);
  g_btor = boolector_btor_mc (g_mc);
  assert (g_btor);
}

static void
finish_mc_test (void)
{
  g_btor = 0;
  boolector_delete_mc (g_mc);
  g_mc = 0;
}

/*------------------------------------------------------------------------*/

static void
test_mcnewdel ()
{
  init_mc_test ();
  finish_mc_test ();
}

/*------------------------------------------------------------------------*/

#define PRINT(NAME, TIME)                                   \
  do                                                        \
  {                                                         \
    char *VAL = boolector_mc_assignment (g_mc, NAME, TIME); \
    fprintf (file, #NAME " = %s\n", VAL);                   \
    boolector_free_mc_assignment (g_mc, VAL);               \
  } while (0)

static void
test_mctoggle ()
{
  int k;

  init_mc_test ();

  BtorNode *bit;

  boolector_set_verbosity_mc (g_mc, 3);

  bit = boolector_latch (g_mc, 1, "counter");

  {
    BtorNode *one  = boolector_one (g_btor, 1);
    BtorNode *zero = boolector_zero (g_btor, 1);
    BtorNode *add  = boolector_add (g_btor, bit, one);
    BtorNode *bad  = boolector_eq (g_btor, bit, one);
    boolector_next (g_mc, bit, add);
    boolector_init (g_mc, bit, zero);
    boolector_bad (g_mc, bad);
    boolector_release (g_btor, one);
    boolector_release (g_btor, zero);
    boolector_release (g_btor, add);
    boolector_release (g_btor, bad);
  }

  k = boolector_bmc (g_mc, 0);
  assert (k < 0);  // can not reach bad within k=0 steps

  k = boolector_bmc (g_mc, 1);
  assert (0 <= k && k <= 1);  // bad reached within k=1 steps

  finish_mc_test ();
}

static void
test_mccount2enablenomodel ()
{
  int k;

  init_mc_test ();

  BtorNode *counter;  // 2-bit state
  BtorNode *enable;   // one boolean control input

  boolector_set_verbosity_mc (g_mc, 3);

  counter = boolector_latch (g_mc, 2, "counter");
  enable  = boolector_input (g_mc, 1, "enable");

  {
    BtorNode *one      = boolector_one (g_btor, 2);
    BtorNode *zero     = boolector_zero (g_btor, 2);
    BtorNode *three    = boolector_const (g_btor, "11");
    BtorNode *add      = boolector_add (g_btor, counter, one);
    BtorNode *ifenable = boolector_cond (g_btor, enable, add, counter);
    BtorNode *bad      = boolector_eq (g_btor, counter, three);
    boolector_next (g_mc, counter, add);  // ifenable);
    boolector_init (g_mc, counter, zero);
    boolector_bad (g_mc, bad);
    boolector_release (g_btor, one);
    boolector_release (g_btor, zero);
    boolector_release (g_btor, three);
    boolector_release (g_btor, add);
    boolector_release (g_btor, ifenable);
    boolector_release (g_btor, bad);
  }

  k = boolector_bmc (g_mc, 1);
  assert (k < 0);  // can not reach bad within k=1 steps

  k = boolector_bmc (g_mc, 5);
  assert (0 <= k && k <= 5);  // bad reached within k=4 steps

  finish_mc_test ();
}

static void
test_mccount2resetenable ()
{
  FILE *file;
  int k, i;

  BtorNode *counter;         // 2-bit state
  BtorNode *enable, *reset;  // two boolean control inputs

  init_mc_test ();

  boolector_enable_trace_gen (g_mc);
  boolector_set_verbosity_mc (g_mc, 3);

  counter = boolector_latch (g_mc, 2, "counter");
  enable  = boolector_input (g_mc, 1, "enable");
  reset   = boolector_input (g_mc, 1, "reset");

  {
    BtorNode *one      = boolector_one (g_btor, 2);
    BtorNode *zero     = boolector_zero (g_btor, 2);
    BtorNode *three    = boolector_const (g_btor, "11");
    BtorNode *add      = boolector_add (g_btor, counter, one);
    BtorNode *ifenable = boolector_cond (g_btor, enable, add, counter);
    BtorNode *ifreset  = boolector_cond (g_btor, reset, ifenable, zero);
    BtorNode *bad      = boolector_eq (g_btor, counter, three);
    boolector_next (g_mc, counter, ifreset);
    boolector_init (g_mc, counter, zero);
    boolector_bad (g_mc, bad);
    boolector_release (g_btor, one);
    boolector_release (g_btor, zero);
    boolector_release (g_btor, three);
    boolector_release (g_btor, add);
    boolector_release (g_btor, ifenable);
    boolector_release (g_btor, ifreset);
    boolector_release (g_btor, bad);
  }

  k = boolector_bmc (g_mc, 2);
  assert (k < 0);  // can not reach bad within k=1 steps

  k = boolector_bmc (g_mc, 4);
  assert (0 <= k && k <= 4);  // bad reached within k=4 steps

  file = fopen ("log/mccount2resetenable.log", "w");
  assert (file);
  fprintf (file, "Bad state property satisfied at k = %d:\n", k);
  for (i = 0; i <= k; i++)
  {
    fprintf (file, "\n");
    fprintf (file, "[ state at time %d ]\n", i);
    PRINT (counter, i);
    fprintf (file, "[ input at time %d ]\n", i);
    PRINT (reset, i);
    PRINT (enable, i);
  }
  fclose (file);

  finish_mc_test ();
}

void
run_mc_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (mcnewdel);
  BTOR_RUN_TEST (mctoggle);
  BTOR_RUN_TEST (mccount2enablenomodel);
  BTOR_RUN_TEST (mccount2resetenable);
}

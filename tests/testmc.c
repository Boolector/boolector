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
  g_mc = boolector_new_mc ();
  boolector_set_verbosity_mc (g_mc, 3);
  g_btor = boolector_btor_mc (g_mc);
}

static void
test_newdel_mc ()
{
}

static void
test_count2_mc ()
{
  BtorNode *counter  = boolector_latch (g_mc, 2, "counter");
  BtorNode *enable   = boolector_input (g_mc, 1, "enable");
  BtorNode *reset    = boolector_input (g_mc, 1, "reset");
  BtorNode *one      = boolector_one (g_btor, 2);
  BtorNode *zero     = boolector_zero (g_btor, 2);
  BtorNode *three    = boolector_const (g_btor, "11");
  BtorNode *add      = boolector_add (g_btor, counter, one);
  BtorNode *ifenable = boolector_cond (g_btor, enable, add, counter);
  BtorNode *ifreset  = boolector_cond (g_btor, reset, ifenable, zero);
  boolector_next (g_mc, counter, ifreset);
  boolector_init (g_mc, counter, zero);
  boolector_bad (g_mc, three);
  boolector_release (g_btor, one);
  boolector_release (g_btor, zero);
  boolector_release (g_btor, three);
  boolector_release (g_btor, add);
  boolector_release (g_btor, ifenable);
  boolector_release (g_btor, ifreset);
  assert (boolector_bmc (g_mc, 1) < 0);
  assert (boolector_bmc (g_mc, 3) == 3);
}

void
run_mc_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (newdel_mc);
  BTOR_RUN_TEST (count2_mc);
}

void
finish_mc_tests (void)
{
  boolector_delete_mc (g_mc);
}

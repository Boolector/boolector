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

void
init_mc_tests (void)
{
  g_mc = boolector_new_mc ();
}

void
run_mc_tests (int argc, char **argv)
{
}

void
finish_mc_tests (void)
{
  boolector_delete_mc (g_mc);
}

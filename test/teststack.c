/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "teststack.h"
#include "testrunner.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static BtorMemMgr *g_mm;

void
init_stack_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

static void
test_init_release_stack (void)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (g_mm, stack);
  BTOR_RELEASE_STACK (stack);
}

static void
test_functionality_stack (void)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (g_mm, stack);
  assert (BTOR_COUNT_STACK (stack) == 0);
  assert (BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 0);
  assert (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (stack, 1);

  assert (BTOR_COUNT_STACK (stack) == 1);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 1);
  assert (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (stack, 2);

  assert (BTOR_COUNT_STACK (stack) == 2);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 2);
  assert (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (stack, 3);

  assert (BTOR_COUNT_STACK (stack) == 3);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 4);
  assert (!BTOR_FULL_STACK (stack));

  assert (BTOR_POP_STACK (stack) == 3);

  assert (BTOR_COUNT_STACK (stack) == 2);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 4);
  assert (!BTOR_FULL_STACK (stack));

  assert (BTOR_POP_STACK (stack) == 2);

  assert (BTOR_COUNT_STACK (stack) == 1);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 4);
  assert (!BTOR_FULL_STACK (stack));

  assert (BTOR_POP_STACK (stack) == 1);

  assert (BTOR_COUNT_STACK (stack) == 0);
  assert (BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 4);
  assert (!BTOR_FULL_STACK (stack));

  BTOR_RELEASE_STACK (stack);
}

static void
test_fit_stack (void)
{
  BtorIntStack stack;
  int32_t i;
  BTOR_INIT_STACK (g_mm, stack);
  for (i = 0; i < 100; i++)
  {
    BTOR_FIT_STACK (stack, i);
    stack.start[i] = i;
  }
  for (i = 0; i < 100; i++) assert (stack.start[i] == i);
  BTOR_FIT_STACK (stack, 999);
  for (i = 100; i < 1000; i++) assert (!stack.start[i]);
  BTOR_RELEASE_STACK (stack);
}

static void
test_reset_stack (void)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (g_mm, stack);
  BTOR_PUSH_STACK (stack, 1);
  BTOR_PUSH_STACK (stack, 2);
  BTOR_PUSH_STACK (stack, 3);
  assert (BTOR_COUNT_STACK (stack) == 3);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 4);
  assert (!BTOR_FULL_STACK (stack));
  BTOR_RESET_STACK (stack);
  assert (BTOR_COUNT_STACK (stack) == 0);
  assert (BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 4);
  assert (!BTOR_FULL_STACK (stack));
  BTOR_RELEASE_STACK (stack);
}

void
run_stack_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (init_release_stack);
  BTOR_RUN_TEST (functionality_stack);
  BTOR_RUN_TEST (reset_stack);
  BTOR_RUN_TEST (fit_stack);
}

void
finish_stack_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}

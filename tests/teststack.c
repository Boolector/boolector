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

#include "teststack.h"
#include "btormem.h"
#include "btorstack.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static BtorMemMgr *g_mm;

void
init_stack_tests (void)
{
  g_mm = btor_new_mem_mgr ();
}

static void
test_init_release_stack (void)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (stack);
  BTOR_RELEASE_STACK (g_mm, stack);
}

static void
test_functionality_stack (void)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (stack);
  assert (BTOR_COUNT_STACK (stack) == 0);
  assert (BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 0);
  assert (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (g_mm, stack, 1);

  assert (BTOR_COUNT_STACK (stack) == 1);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 1);
  assert (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (g_mm, stack, 2);

  assert (BTOR_COUNT_STACK (stack) == 2);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 2);
  assert (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (g_mm, stack, 3);

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

  BTOR_RELEASE_STACK (g_mm, stack);
}

static void
test_fit_stack (void)
{
  BtorIntStack stack;
  int i;
  BTOR_INIT_STACK (stack);
  for (i = 0; i < 100; i++)
  {
    BTOR_FIT_STACK (g_mm, stack, i);
    stack.start[i] = i;
  }
  for (i = 0; i < 100; i++) assert (stack.start[i] == i);
  BTOR_FIT_STACK (g_mm, stack, 999);
  for (i = 100; i < 1000; i++) assert (!stack.start[i]);
  BTOR_RELEASE_STACK (g_mm, stack);
}

static void
test_reset_stack (void)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (g_mm, stack, 1);
  BTOR_PUSH_STACK (g_mm, stack, 2);
  BTOR_PUSH_STACK (g_mm, stack, 3);
  assert (BTOR_COUNT_STACK (stack) == 3);
  assert (!BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 4);
  assert (!BTOR_FULL_STACK (stack));
  BTOR_RESET_STACK (stack);
  assert (BTOR_COUNT_STACK (stack) == 0);
  assert (BTOR_EMPTY_STACK (stack));
  assert (BTOR_SIZE_STACK (stack) == 4);
  assert (!BTOR_FULL_STACK (stack));
  BTOR_RELEASE_STACK (g_mm, stack);
}

void
run_stack_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (init_release_stack);
  BTOR_RUN_TEST (functionality_stack);
  BTOR_RUN_TEST (reset_stack);
  BTOR_RUN_TEST (fit_stack);
}

void
finish_stack_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}

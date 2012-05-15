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

#include "testqueue.h"
#include "btormem.h"
#include "btorqueue.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static BtorMemMgr *g_mm;

void
init_queue_tests (void)
{
  g_mm = btor_new_mem_mgr ();
}

static void
test_init_release_queue (void)
{
  BtorIntQueue queue;
  BTOR_INIT_QUEUE (queue);
  BTOR_RELEASE_QUEUE (g_mm, queue);
}

static void
test_functionality_queue (void)
{
  BtorIntQueue queue;

  BTOR_INIT_QUEUE (queue);

  assert (BTOR_COUNT_QUEUE (queue) == 0);
  assert (BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_SIZE_QUEUE (queue) == 0);
  assert (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (g_mm, queue, 1);

  assert (BTOR_COUNT_QUEUE (queue) == 1);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (g_mm, queue, 2);

  assert (BTOR_COUNT_QUEUE (queue) == 2);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (g_mm, queue, 3);

  assert (BTOR_COUNT_QUEUE (queue) == 3);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (!BTOR_FULL_QUEUE (queue));

  assert (BTOR_DEQUEUE (queue) == 1);

  assert (BTOR_COUNT_QUEUE (queue) == 2);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (!BTOR_FULL_QUEUE (queue));

  assert (BTOR_DEQUEUE (queue) == 2);

  assert (BTOR_COUNT_QUEUE (queue) == 1);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (!BTOR_FULL_QUEUE (queue));

  assert (BTOR_DEQUEUE (queue) == 3);

  assert (BTOR_COUNT_QUEUE (queue) == 0);
  assert (BTOR_EMPTY_QUEUE (queue));
  assert (!BTOR_FULL_QUEUE (queue));

  assert (BTOR_SIZE_QUEUE (queue) <= 4);

  BTOR_RELEASE_QUEUE (g_mm, queue);
}

static void
test_reset_queue (void)
{
  BtorIntQueue queue;
  int i, j, k;

  BTOR_INIT_QUEUE (queue);

  for (i = 0; i < 10000; i++) BTOR_ENQUEUE (g_mm, queue, i);

  assert (BTOR_COUNT_QUEUE (queue) == i);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_SIZE_QUEUE (queue) == (1 << 14));
  assert (!BTOR_FULL_QUEUE (queue));

  for (j = 0; j < 5000; j++) assert (BTOR_DEQUEUE (queue) == j);

  for (k = 0; k < 100; k++)
  {
    for (j = 0; j < 5000; j++) BTOR_ENQUEUE (g_mm, queue, j);

    for (j = 0; j < 5000; j++) (void) BTOR_DEQUEUE (queue);
  }

  for (; i < (1 << 14); i++) BTOR_ENQUEUE (g_mm, queue, i);

  BTOR_RESET_QUEUE (queue);

  assert (BTOR_COUNT_QUEUE (queue) == 0);
  assert (BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_SIZE_QUEUE (queue) == (1 << 14));
  assert (!BTOR_FULL_QUEUE (queue));

  BTOR_RELEASE_QUEUE (g_mm, queue);
}

void
run_queue_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (init_release_queue);
  BTOR_RUN_TEST (functionality_queue);
  BTOR_RUN_TEST (reset_queue);
}

void
finish_queue_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}

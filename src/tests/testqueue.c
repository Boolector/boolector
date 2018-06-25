/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testqueue.h"
#include "testrunner.h"
#include "utils/btormem.h"
#include "utils/btorqueue.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

BTOR_DECLARE_QUEUE (BtorUInt, uint32_t);

#include <assert.h>

static BtorMemMgr *g_mm;

void
init_queue_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

static void
test_init_release_queue (void)
{
  BtorUIntQueue queue;
  BTOR_INIT_QUEUE (g_mm, queue);
  BTOR_RELEASE_QUEUE (queue);
}

static void
test_functionality_queue (void)
{
  BtorUIntQueue queue;

  BTOR_INIT_QUEUE (g_mm, queue);

  assert (BTOR_COUNT_QUEUE (queue) == 0);
  assert (BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_SIZE_QUEUE (queue) == 0);
  assert (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (queue, 1);

  assert (BTOR_COUNT_QUEUE (queue) == 1);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (queue, 2);

  assert (BTOR_COUNT_QUEUE (queue) == 2);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (queue, 3);

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

  BTOR_RELEASE_QUEUE (queue);
}

static void
test_reset_queue (void)
{
  BtorUIntQueue queue;
  uint32_t i, j, k;

  BTOR_INIT_QUEUE (g_mm, queue);

  for (i = 0; i < 10000; i++) BTOR_ENQUEUE (queue, i);

  assert (BTOR_COUNT_QUEUE (queue) == i);
  assert (!BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_SIZE_QUEUE (queue) == (1 << 14));
  assert (!BTOR_FULL_QUEUE (queue));

  for (j = 0; j < 5000; j++) assert (BTOR_DEQUEUE (queue) == j);

  for (k = 0; k < 100; k++)
  {
    for (j = 0; j < 5000; j++) BTOR_ENQUEUE (queue, j);

    for (j = 0; j < 5000; j++) (void) BTOR_DEQUEUE (queue);
  }

  for (; i < (1 << 14); i++) BTOR_ENQUEUE (queue, i);

  BTOR_RESET_QUEUE (queue);

  assert (BTOR_COUNT_QUEUE (queue) == 0);
  assert (BTOR_EMPTY_QUEUE (queue));
  assert (BTOR_SIZE_QUEUE (queue) == (1 << 14));
  assert (!BTOR_FULL_QUEUE (queue));

  BTOR_RELEASE_QUEUE (queue);
}

void
run_queue_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (init_release_queue);
  BTOR_RUN_TEST (functionality_queue);
  BTOR_RUN_TEST (reset_queue);
}

void
finish_queue_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}

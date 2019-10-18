/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/btorqueue.h"
}

BTOR_DECLARE_QUEUE (BtorUInt, uint32_t);

class TestQueue : public TestMm
{
};

TEST_F (TestQueue, init_release)
{
  BtorUIntQueue queue;
  BTOR_INIT_QUEUE (d_mm, queue);
  BTOR_RELEASE_QUEUE (queue);
}

TEST_F (TestQueue, functionality)
{
  BtorUIntQueue queue;

  BTOR_INIT_QUEUE (d_mm, queue);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), 0u);
  ASSERT_TRUE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_EQ (BTOR_SIZE_QUEUE (queue), 0u);
  ASSERT_TRUE (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (queue, 1);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), 1u);
  ASSERT_FALSE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_TRUE (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (queue, 2);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), 2u);
  ASSERT_FALSE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_TRUE (BTOR_FULL_QUEUE (queue));

  BTOR_ENQUEUE (queue, 3);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), 3u);
  ASSERT_FALSE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_FALSE (BTOR_FULL_QUEUE (queue));

  ASSERT_EQ (BTOR_DEQUEUE (queue), 1u);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), 2u);
  ASSERT_FALSE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_FALSE (BTOR_FULL_QUEUE (queue));

  ASSERT_EQ (BTOR_DEQUEUE (queue), 2u);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), 1u);
  ASSERT_FALSE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_FALSE (BTOR_FULL_QUEUE (queue));

  ASSERT_EQ (BTOR_DEQUEUE (queue), 3u);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), 0u);
  ASSERT_TRUE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_FALSE (BTOR_FULL_QUEUE (queue));

  ASSERT_LE (BTOR_SIZE_QUEUE (queue), 4u);

  BTOR_RELEASE_QUEUE (queue);
}

TEST_F (TestQueue, reset)
{
  BtorUIntQueue queue;
  uint32_t i, j, k;

  BTOR_INIT_QUEUE (d_mm, queue);

  for (i = 0; i < 10000; i++) BTOR_ENQUEUE (queue, i);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), i);
  ASSERT_FALSE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_EQ (BTOR_SIZE_QUEUE (queue), (uint32_t) (1 << 14));
  ASSERT_FALSE (BTOR_FULL_QUEUE (queue));

  for (j = 0; j < 5000; j++)
  {
    ASSERT_EQ (BTOR_DEQUEUE (queue), j);
  }

  for (k = 0; k < 100; k++)
  {
    for (j = 0; j < 5000; j++) BTOR_ENQUEUE (queue, j);

    for (j = 0; j < 5000; j++) (void) BTOR_DEQUEUE (queue);
  }

  for (; i < (1 << 14); i++) BTOR_ENQUEUE (queue, i);

  BTOR_RESET_QUEUE (queue);

  ASSERT_EQ (BTOR_COUNT_QUEUE (queue), 0u);
  ASSERT_TRUE (BTOR_EMPTY_QUEUE (queue));
  ASSERT_EQ (BTOR_SIZE_QUEUE (queue), (uint32_t) (1 << 14));
  ASSERT_FALSE (BTOR_FULL_QUEUE (queue));

  BTOR_RELEASE_QUEUE (queue);
}

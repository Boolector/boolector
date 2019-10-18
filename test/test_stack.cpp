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
#include "utils/btorstack.h"
}

class TestStack : public TestMm
{
};

TEST_F (TestStack, init_release)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (d_mm, stack);
  BTOR_RELEASE_STACK (stack);
}

TEST_F (TestStack, functionality)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (d_mm, stack);
  ASSERT_EQ (BTOR_COUNT_STACK (stack), 0u);
  ASSERT_TRUE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 0u);
  ASSERT_TRUE (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (stack, 1);

  ASSERT_EQ (BTOR_COUNT_STACK (stack), 1u);
  ASSERT_FALSE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 1u);
  ASSERT_TRUE (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (stack, 2);

  ASSERT_EQ (BTOR_COUNT_STACK (stack), 2u);
  ASSERT_FALSE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 2u);
  ASSERT_TRUE (BTOR_FULL_STACK (stack));

  BTOR_PUSH_STACK (stack, 3);

  ASSERT_EQ (BTOR_COUNT_STACK (stack), 3u);
  ASSERT_FALSE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 4u);
  ASSERT_FALSE (BTOR_FULL_STACK (stack));

  ASSERT_EQ (BTOR_POP_STACK (stack), 3);

  ASSERT_EQ (BTOR_COUNT_STACK (stack), 2u);
  ASSERT_FALSE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 4u);
  ASSERT_FALSE (BTOR_FULL_STACK (stack));

  ASSERT_EQ (BTOR_POP_STACK (stack), 2);

  ASSERT_EQ (BTOR_COUNT_STACK (stack), 1u);
  ASSERT_FALSE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 4u);
  ASSERT_FALSE (BTOR_FULL_STACK (stack));

  ASSERT_EQ (BTOR_POP_STACK (stack), 1);

  ASSERT_EQ (BTOR_COUNT_STACK (stack), 0u);
  ASSERT_TRUE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 4u);
  ASSERT_FALSE (BTOR_FULL_STACK (stack));

  BTOR_RELEASE_STACK (stack);
}

TEST_F (TestStack, fit)
{
  BtorIntStack stack;
  int32_t i;
  BTOR_INIT_STACK (d_mm, stack);
  for (i = 0; i < 100; i++)
  {
    BTOR_FIT_STACK (stack, i);
    stack.start[i] = i;
  }
  for (i = 0; i < 100; i++)
  {
    ASSERT_EQ (stack.start[i], i);
  }
  BTOR_FIT_STACK (stack, 999);
  for (i = 100; i < 1000; i++)
  {
    ASSERT_FALSE (stack.start[i]);
  }
  BTOR_RELEASE_STACK (stack);
}

TEST_F (TestStack, reset)
{
  BtorIntStack stack;
  BTOR_INIT_STACK (d_mm, stack);
  BTOR_PUSH_STACK (stack, 1);
  BTOR_PUSH_STACK (stack, 2);
  BTOR_PUSH_STACK (stack, 3);
  ASSERT_EQ (BTOR_COUNT_STACK (stack), 3u);
  ASSERT_FALSE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 4u);
  ASSERT_FALSE (BTOR_FULL_STACK (stack));
  BTOR_RESET_STACK (stack);
  ASSERT_EQ (BTOR_COUNT_STACK (stack), 0u);
  ASSERT_TRUE (BTOR_EMPTY_STACK (stack));
  ASSERT_EQ (BTOR_SIZE_STACK (stack), 4u);
  ASSERT_FALSE (BTOR_FULL_STACK (stack));
  BTOR_RELEASE_STACK (stack);
}

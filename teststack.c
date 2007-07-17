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
}

void
finish_stack_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}

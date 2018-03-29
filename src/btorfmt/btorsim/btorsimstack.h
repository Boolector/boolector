/**
 *  BtorFMT: A tool package for the BTOR format.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2015-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of the BtorFMT package.
 *  See LICENSE.txt for more information on using this software.
 */

#ifndef BTORSIMSTACK_H_INCLUDED
#define BTORSIMSTACK_H_INCLUDED

#include "btorsimmem.h"

#define BTORSIM_DECLARE_STACK(name, type) \
  typedef struct name##Stack name##Stack; \
  struct name##Stack                      \
  {                                       \
    type *start;                          \
    type *top;                            \
    type *end;                            \
  }

BTORSIM_DECLARE_STACK (BtorInt, int32_t);
BTORSIM_DECLARE_STACK (BtorUInt, uint32_t);
BTORSIM_DECLARE_STACK (BtorChar, char);
BTORSIM_DECLARE_STACK (BtorCharPtr, char *);
BTORSIM_DECLARE_STACK (BtorVoidPtr, void *);

#define BTORSIM_INIT_STACK(stack) \
  do                              \
  {                               \
    (stack).start = 0;            \
    (stack).top   = 0;            \
    (stack).end   = 0;            \
  } while (0)

#define BTORSIM_COUNT_STACK(stack) ((stack).top - (stack).start)
#define BTORSIM_SIZE_STACK(stack) ((stack).end - (stack).start)
#define BTORSIM_EMPTY_STACK(stack) ((stack).top == (stack).start)
#define BTORSIM_FULL_STACK(stack) ((stack).top == (stack).end)
#define BTORSIM_RESET_STACK(stack) ((stack).top = (stack).start)

#define BTORSIM_RELEASE_STACK(stack) \
  do                                 \
  {                                  \
    BTORSIM_DELETE ((stack).start);  \
    BTORSIM_INIT_STACK ((stack));    \
  } while (0)

#define BTORSIM_ENLARGE(p, o, n)          \
  do                                      \
  {                                       \
    size_t internaln = (o) ? 2 * (o) : 1; \
    BTORSIM_REALLOC ((p), internaln);     \
    (n) = internaln;                      \
  } while (0)

#define BTORSIM_ENLARGE_STACK(stack)                         \
  do                                                         \
  {                                                          \
    size_t old_size  = BTORSIM_SIZE_STACK (stack), new_size; \
    size_t old_count = BTORSIM_COUNT_STACK (stack);          \
    BTORSIM_ENLARGE ((stack).start, old_size, new_size);     \
    (stack).top = (stack).start + old_count;                 \
    (stack).end = (stack).start + new_size;                  \
  } while (0)

#define BTORSIM_PUSH_STACK(stack, elem)                                \
  do                                                                   \
  {                                                                    \
    if (BTORSIM_FULL_STACK ((stack))) BTORSIM_ENLARGE_STACK ((stack)); \
    *((stack).top++) = (elem);                                         \
  } while (0)

#define BTORSIM_POP_STACK(stack) \
  (assert (!BTORSIM_EMPTY_STACK (stack)), (*--(stack).top))

#define BTORSIM_PEEK_STACK(stack, idx) \
  (assert ((idx) < BTORSIM_COUNT_STACK (stack)), (stack).start[idx])

#define BTORSIM_POKE_STACK(stack, idx, elem)      \
  do                                              \
  {                                               \
    assert ((idx) < BTORSIM_COUNT_STACK (stack)); \
    (stack).start[idx] = (elem);                  \
  } while (0)

#endif

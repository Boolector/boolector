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

#ifndef BTORFMTSTACK_H_INCLUDED
#define BTORFMTSTACK_H_INCLUDED

#include "btorfmtmem.h"

#define BTORFMT_DECLARE_STACK(name, type) \
  typedef struct name##Stack name##Stack; \
  struct name##Stack                      \
  {                                       \
    type *start;                          \
    type *top;                            \
    type *end;                            \
  }

BTORFMT_DECLARE_STACK (BtorChar, char);
BTORFMT_DECLARE_STACK (BtorCharPtr, char *);
BTORFMT_DECLARE_STACK (BtorVoidPtr, void *);

#define BTORFMT_INIT_STACK(stack) \
  do                              \
  {                               \
    (stack).start = 0;            \
    (stack).top   = 0;            \
    (stack).end   = 0;            \
  } while (0)

#define BTORFMT_COUNT_STACK(stack) ((stack).top - (stack).start)
#define BTORFMT_SIZE_STACK(stack) ((stack).end - (stack).start)
#define BTORFMT_EMPTY_STACK(stack) ((stack).top == (stack).start)
#define BTORFMT_FULL_STACK(stack) ((stack).top == (stack).end)
#define BTORFMT_RESET_STACK(stack) ((stack).top = (stack).start)

#define BTORFMT_RELEASE_STACK(stack) \
  do                                 \
  {                                  \
    BTORFMT_DELETE ((stack).start);  \
    BTORFMT_INIT_STACK ((stack));    \
  } while (0)

#define BTORFMT_ENLARGE(p, o, n)          \
  do                                      \
  {                                       \
    size_t internaln = (o) ? 2 * (o) : 1; \
    BTORFMT_REALLOC ((p), internaln);     \
    (n) = internaln;                      \
  } while (0)

#define BTORFMT_ENLARGE_STACK(stack)                         \
  do                                                         \
  {                                                          \
    size_t old_size  = BTORFMT_SIZE_STACK (stack), new_size; \
    size_t old_count = BTORFMT_COUNT_STACK (stack);          \
    BTORFMT_ENLARGE ((stack).start, old_size, new_size);     \
    (stack).top = (stack).start + old_count;                 \
    (stack).end = (stack).start + new_size;                  \
  } while (0)

#define BTORFMT_PUSH_STACK(stack, elem)                                \
  do                                                                   \
  {                                                                    \
    if (BTORFMT_FULL_STACK ((stack))) BTORFMT_ENLARGE_STACK ((stack)); \
    *((stack).top++) = (elem);                                         \
  } while (0)

#define BTORFMT_POP_STACK(stack) \
  (assert (!BTORFMT_EMPTY_STACK (stack)), (*--(stack).top))

#define BTORFMT_PEEK_STACK(stack, idx) \
  (assert ((idx) < BTORFMT_COUNT_STACK (stack)), (stack).start[idx])

#define BTORFMT_POKE_STACK(stack, idx, elem)      \
  do                                              \
  {                                               \
    assert ((idx) < BTORFMT_COUNT_STACK (stack)); \
    (stack).start[idx] = (elem);                  \
  } while (0)

#endif

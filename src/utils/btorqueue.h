/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOR_QUEUE_H_INCLUDED
#define BTOR_QUEUE_H_INCLUDED

#include "utils/btormem.h"

#include <assert.h>

#define BTOR_DECLARE_QUEUE(name, type)    \
  typedef struct name##Queue name##Queue; \
  struct name##Queue                      \
  {                                       \
    BtorMemMgr* mm;                       \
    type* start;                          \
    type* head;                           \
    type* tail;                           \
    type* end;                            \
  }

#define BTOR_INIT_QUEUE(mem, queue) \
  do                                \
  {                                 \
    (queue).mm    = mem;            \
    (queue).start = 0;              \
    (queue).head  = 0;              \
    (queue).tail  = 0;              \
    (queue).end   = 0;              \
  } while (0)

#define BTOR_COUNT_QUEUE(queue) \
  (assert ((queue).mm), (size_t) ((queue).tail - (queue).head))
#define BTOR_EMPTY_QUEUE(queue) \
  (assert ((queue).mm), (queue).tail == (queue).head)

#define BTOR_RESET_QUEUE(queue)                  \
  do                                             \
  {                                              \
    assert ((queue).mm);                         \
    (queue).head = (queue).tail = (queue).start; \
  } while (0)

#define BTOR_SIZE_QUEUE(queue) \
  (assert ((queue).mm), (size_t) ((queue).end - (queue).start))
#define BTOR_FULL_QUEUE(queue) \
  (assert ((queue).mm), (queue).tail == (queue).end)

#define BTOR_RELEASE_QUEUE(queue)                                        \
  do                                                                     \
  {                                                                      \
    assert ((queue).mm);                                                 \
    BTOR_DELETEN ((queue).mm, (queue).start, BTOR_SIZE_QUEUE ((queue))); \
    BTOR_INIT_QUEUE ((queue).mm, queue);                                 \
  } while (0)

#define BTOR_ENLARGE_QUEUE(queue)                                 \
  do                                                              \
  {                                                               \
    assert ((queue).mm);                                          \
    uint32_t old_size     = BTOR_SIZE_QUEUE (queue), new_size;    \
    uint32_t old_tail_pos = (queue).tail - (queue).start;         \
    uint32_t old_head_pos = (queue).head - (queue).start;         \
    BTOR_ENLARGE ((queue).mm, (queue).start, old_size, new_size); \
    (queue).tail = (queue).start + old_tail_pos;                  \
    (queue).head = (queue).start + old_head_pos;                  \
    (queue).end  = (queue).start + new_size;                      \
  } while (0)

#define BTOR_MOVE_QUEUE(queue)                                            \
  do                                                                      \
  {                                                                       \
    assert ((queue).mm);                                                  \
    uint32_t offset = (queue).head - (queue).start;                       \
    uint32_t count  = BTOR_COUNT_QUEUE ((queue));                         \
    memmove ((queue).start, (queue).head, count * sizeof *(queue).start); \
    (queue).head = (queue).start;                                         \
    (queue).tail -= offset;                                               \
  } while (0)

#define BTOR_ENQUEUE(queue, elem)                                 \
  do                                                              \
  {                                                               \
    assert ((queue).mm);                                          \
    if (BTOR_FULL_QUEUE ((queue)))                                \
    {                                                             \
      if (2 * BTOR_COUNT_QUEUE (queue) < BTOR_SIZE_QUEUE (queue)) \
        BTOR_MOVE_QUEUE ((queue));                                \
      else                                                        \
        BTOR_ENLARGE_QUEUE ((queue));                             \
    }                                                             \
    assert ((queue).tail < (queue).end);                          \
    *(queue).tail++ = (elem);                                     \
  } while (0)

#define BTOR_DEQUEUE(queue) (assert ((queue).mm), *(queue).head++)

BTOR_DECLARE_QUEUE (BtorInt, int32_t);

#endif

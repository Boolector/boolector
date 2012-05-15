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

#ifndef BTOR_QUEUE_H_INCLUDED
#define BTOR_QUEUE_H_INCLUDED

#include "btormem.h"

#include <assert.h>

#define BTOR_DECLARE_QUEUE(name, type)                \
  typedef struct Btor##name##Queue Btor##name##Queue; \
  struct Btor##name##Queue                            \
  {                                                   \
    type* start;                                      \
    type* head;                                       \
    type* tail;                                       \
    type* end;                                        \
  }

#define BTOR_INIT_QUEUE(queue) \
  do                           \
  {                            \
    (queue).start = 0;         \
    (queue).head  = 0;         \
    (queue).tail  = 0;         \
    (queue).end   = 0;         \
  } while (0)

#define BTOR_COUNT_QUEUE(queue) ((queue).tail - (queue).head)
#define BTOR_EMPTY_QUEUE(queue) ((queue).tail == (queue).head)

#define BTOR_RESET_QUEUE(queue)                  \
  do                                             \
  {                                              \
    (queue).head = (queue).tail = (queue).start; \
  } while (0)

#define BTOR_SIZE_QUEUE(queue) ((queue).end - (queue).start)
#define BTOR_FULL_QUEUE(queue) ((queue).tail == (queue).end)

#define BTOR_RELEASE_QUEUE(mm, queue)                              \
  do                                                               \
  {                                                                \
    BTOR_DELETEN ((mm), (queue).start, BTOR_SIZE_QUEUE ((queue))); \
    BTOR_INIT_QUEUE (queue);                                       \
  } while (0)

#define BTOR_ENLARGE_QUEUE(mm, queue)                       \
  do                                                        \
  {                                                         \
    int old_size     = BTOR_SIZE_QUEUE (queue), new_size;   \
    int old_tail_pos = (queue).tail - (queue).start;        \
    int old_head_pos = (queue).head - (queue).start;        \
    BTOR_ENLARGE ((mm), (queue).start, old_size, new_size); \
    (queue).tail = (queue).start + old_tail_pos;            \
    (queue).head = (queue).start + old_head_pos;            \
    (queue).end  = (queue).start + new_size;                \
  } while (0)

#define BTOR_MOVE_QUEUE(mm, queue)                                        \
  do                                                                      \
  {                                                                       \
    int offset = (queue).head - (queue).start;                            \
    int count  = BTOR_COUNT_QUEUE ((queue));                              \
    memmove ((queue).start, (queue).head, count * sizeof *(queue).start); \
    (queue).head = (queue).start;                                         \
    (queue).tail -= offset;                                               \
  } while (0)

#define BTOR_ENQUEUE(mm, queue, elem)                             \
  do                                                              \
  {                                                               \
    if (BTOR_FULL_QUEUE ((queue)))                                \
    {                                                             \
      if (2 * BTOR_COUNT_QUEUE (queue) < BTOR_SIZE_QUEUE (queue)) \
        BTOR_MOVE_QUEUE ((mm), (queue));                          \
      else                                                        \
        BTOR_ENLARGE_QUEUE ((mm), (queue));                       \
    }                                                             \
    assert ((queue).tail < (queue).end);                          \
    *(queue).tail++ = (elem);                                     \
  } while (0)

#define BTOR_DEQUEUE(queue) (*(queue).head++)

BTOR_DECLARE_QUEUE (Int, int);

#endif

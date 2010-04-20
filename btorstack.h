/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2010  Robert Daniel Brummayer, Armin Biere
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

#ifndef BTOR_STACK_H_INCLUDED
#define BTOR_STACK_H_INCLUDED

#include "btormem.h"

#include <assert.h>

#define BTOR_DECLARE_STACK(name, type)                \
  typedef struct Btor##name##Stack Btor##name##Stack; \
  struct Btor##name##Stack                            \
  {                                                   \
    type *start;                                      \
    type *top;                                        \
    type *end;                                        \
  }

#define BTOR_INIT_STACK(stack) \
  do                           \
  {                            \
    (stack).start = 0;         \
    (stack).top   = 0;         \
    (stack).end   = 0;         \
  } while (0)

#define BTOR_COUNT_STACK(stack) ((stack).top - (stack).start)
#define BTOR_EMPTY_STACK(stack) ((stack).top == (stack).start)
#define BTOR_RESET_STACK(stack)  \
  do                             \
  {                              \
    (stack).top = (stack).start; \
  } while (0)

#define BTOR_SIZE_STACK(stack) ((stack).end - (stack).start)
#define BTOR_FULL_STACK(stack) ((stack).top == (stack).end)

#define BTOR_RELEASE_STACK(mm, stack)                              \
  do                                                               \
  {                                                                \
    BTOR_DELETEN ((mm), (stack).start, BTOR_SIZE_STACK ((stack))); \
    BTOR_INIT_STACK ((stack));                                     \
  } while (0)

#define BTOR_ENLARGE_STACK(mm, stack)                       \
  do                                                        \
  {                                                         \
    int old_size  = BTOR_SIZE_STACK (stack), new_size;      \
    int old_count = BTOR_COUNT_STACK (stack);               \
    BTOR_ENLARGE ((mm), (stack).start, old_size, new_size); \
    (stack).top = (stack).start + old_count;                \
    (stack).end = (stack).start + new_size;                 \
  } while (0)

#define BTOR_PUSH_STACK(mm, stack, elem)                               \
  do                                                                   \
  {                                                                    \
    if (BTOR_FULL_STACK ((stack))) BTOR_ENLARGE_STACK ((mm), (stack)); \
    *((stack).top++) = (elem);                                         \
  } while (0)

#define BTOR_POP_STACK(stack) (*--(stack).top)

BTOR_DECLARE_STACK (Int, int);
BTOR_DECLARE_STACK (Char, char);
BTOR_DECLARE_STACK (CharPtr, char *);
BTOR_DECLARE_STACK (VoidPtr, void *);

#endif

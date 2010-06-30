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

#ifndef BTORMEM_H_INCLUDED
#define BTORMEM_H_INCLUDED

#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

#define BTOR_NEWN(mm, ptr, nelems)                        \
  do                                                      \
  {                                                       \
    (ptr) = btor_malloc ((mm), (nelems) * sizeof *(ptr)); \
  } while (0)

#define BTOR_CNEWN(mm, ptr, nelems)                      \
  do                                                     \
  {                                                      \
    (ptr) = btor_calloc ((mm), (nelems), sizeof *(ptr)); \
  } while (0)

#define BTOR_CLRN(ptr, nelems)                   \
  do                                             \
  {                                              \
    memset ((ptr), 0, (nelems) * sizeof *(ptr)); \
  } while (0)

#define BTOR_DELETEN(mm, ptr, nelems)                  \
  do                                                   \
  {                                                    \
    btor_free ((mm), (ptr), (nelems) * sizeof *(ptr)); \
  } while (0)

#define BTOR_REALLOC(mm, p, o, n)                                             \
  do                                                                          \
  {                                                                           \
    (p) = btor_realloc ((mm), (p), ((o) * sizeof *(p)), ((n) * sizeof *(p))); \
  } while (0)

#define BTOR_NEW(mm, ptr) BTOR_NEWN ((mm), (ptr), 1)
#define BTOR_CNEW(mm, ptr) BTOR_CNEWN ((mm), (ptr), 1)
#define BTOR_CLR(ptr) BTOR_CLRN ((ptr), 1)
#define BTOR_DELETE(mm, ptr) BTOR_DELETEN ((mm), (ptr), 1)

#define BTOR_ENLARGE(mm, p, o, n)             \
  do                                          \
  {                                           \
    int internaln = (o) ? 2 * (o) : 1;        \
    BTOR_REALLOC ((mm), (p), (o), internaln); \
    (n) = internaln;                          \
  } while (0)

struct BtorMemMgr
{
  size_t allocated;
  size_t maxallocated;
  size_t limitallocated;
  int limited;
};

typedef struct BtorMemMgr BtorMemMgr;

BtorMemMgr *btor_new_mem_mgr (void);

void *btor_malloc (BtorMemMgr *mm, size_t size);

void *btor_realloc (BtorMemMgr *mm, void *, size_t oldsz, size_t newsz);

void *btor_calloc (BtorMemMgr *mm, size_t nobj, size_t size);

void btor_free (BtorMemMgr *mm, void *p, size_t freed);

char *btor_strdup (BtorMemMgr *mm, const char *str);

void btor_freestr (BtorMemMgr *mm, char *str);

void btor_delete_mem_mgr (BtorMemMgr *mm);

size_t btor_parse_error_message_length (const char *name,
                                        const char *fmt,
                                        va_list ap);

char *btor_parse_error_message (BtorMemMgr *,
                                const char *name,
                                int lineno,
                                const char *fmt,
                                va_list,
                                size_t bytes);
#endif

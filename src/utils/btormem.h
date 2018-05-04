/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMEM_H_INCLUDED
#define BTORMEM_H_INCLUDED

#include <stdarg.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#define BTOR_NEWN(mm, ptr, nelems)                                          \
  do                                                                        \
  {                                                                         \
    (ptr) = (typeof(ptr)) btor_mem_malloc ((mm), (nelems) * sizeof *(ptr)); \
  } while (0)

#define BTOR_CNEWN(mm, ptr, nelems)                                        \
  do                                                                       \
  {                                                                        \
    (ptr) = (typeof(ptr)) btor_mem_calloc ((mm), (nelems), sizeof *(ptr)); \
  } while (0)

#define BTOR_CLRN(ptr, nelems)                   \
  do                                             \
  {                                              \
    memset ((ptr), 0, (nelems) * sizeof *(ptr)); \
  } while (0)

#define BTOR_DELETEN(mm, ptr, nelems)                      \
  do                                                       \
  {                                                        \
    btor_mem_free ((mm), (ptr), (nelems) * sizeof *(ptr)); \
  } while (0)

#define BTOR_REALLOC(mm, p, o, n)                             \
  do                                                          \
  {                                                           \
    (p) = (typeof(p)) btor_mem_realloc (                      \
        (mm), (p), ((o) * sizeof *(p)), ((n) * sizeof *(p))); \
  } while (0)

#define BTOR_NEW(mm, ptr) BTOR_NEWN ((mm), (ptr), 1)

#define BTOR_CNEW(mm, ptr) BTOR_CNEWN ((mm), (ptr), 1)

#define BTOR_CLR(ptr) BTOR_CLRN ((ptr), 1)

#define BTOR_DELETE(mm, ptr) BTOR_DELETEN ((mm), (ptr), 1)

#define BTOR_ENLARGE(mm, p, o, n)             \
  do                                          \
  {                                           \
    size_t internaln = (o) ? 2 * (o) : 1;     \
    BTOR_REALLOC ((mm), (p), (o), internaln); \
    (n) = internaln;                          \
  } while (0)

/*------------------------------------------------------------------------*/

struct BtorMemMgr
{
  size_t allocated;
  size_t maxallocated;
  size_t sat_allocated;
  size_t sat_maxallocated;
};

typedef struct BtorMemMgr BtorMemMgr;

/*------------------------------------------------------------------------*/

BtorMemMgr *btor_mem_mgr_new (void);

void btor_mem_mgr_delete (BtorMemMgr *mm);

void *btor_mem_sat_malloc (BtorMemMgr *mm, size_t size);

void *btor_mem_sat_realloc (BtorMemMgr *mm, void *, size_t oldsz, size_t newsz);

void btor_mem_sat_free (BtorMemMgr *mm, void *p, size_t freed);

void *btor_mem_malloc (BtorMemMgr *mm, size_t size);

void *btor_mem_realloc (BtorMemMgr *mm, void *, size_t oldsz, size_t newsz);

void *btor_mem_calloc (BtorMemMgr *mm, size_t nobj, size_t size);

void btor_mem_free (BtorMemMgr *mm, void *p, size_t freed);

char *btor_mem_strdup (BtorMemMgr *mm, const char *str);

void btor_mem_freestr (BtorMemMgr *mm, char *str);

size_t btor_mem_parse_error_msg_length (const char *name,
                                        const char *fmt,
                                        va_list ap);

char *btor_mem_parse_error_msg (BtorMemMgr *,
                                const char *name,
                                int32_t lineno,
                                int32_t columnno,
                                const char *fmt,
                                va_list,
                                size_t bytes);
#endif

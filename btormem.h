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
};

typedef struct BtorMemMgr BtorMemMgr;

BtorMemMgr *btor_new_mem_mgr (void);

void *btor_malloc (BtorMemMgr *mm, size_t size);

void *btor_realloc (BtorMemMgr *mm, void *, size_t old, size_t new);

void *btor_calloc (BtorMemMgr *mm, size_t nobj, size_t size);

void btor_free (BtorMemMgr *mm, void *p, size_t freed);

char *btor_strdup (BtorMemMgr *mm, const char *str);

void btor_freestr (BtorMemMgr *mm, char *str);

void btor_delete_mem_mgr (BtorMemMgr *mm);

char *btor_parse_error_message (
    BtorMemMgr *, const char *name, int lineno, const char *fmt, va_list);

#endif

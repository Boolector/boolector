#include "btormem.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_ABORT_MEM(cond, msg)          \
  do                                       \
  {                                        \
    if (!(cond)) break;                    \
    fputs ("[btormem] " msg "\n", stderr); \
    abort ();                              \
  } while (0)

#define ADJUST()                                                            \
  do                                                                        \
  {                                                                         \
    if (mm->maxallocated < mm->allocated) mm->maxallocated = mm->allocated; \
  } while (0)

BtorMemMgr *
btor_new_mem_mgr (void)
{
  BtorMemMgr *mm   = (BtorMemMgr *) malloc (sizeof (BtorMemMgr));
  mm->allocated    = 0;
  mm->maxallocated = 0;
  return mm;
}

void *
btor_malloc (BtorMemMgr *mm, size_t size)
{
  void *result;
  assert (mm != NULL);
  result = malloc (size);
  BTOR_ABORT_MEM (result == NULL, "out of memory in 'btor_malloc'");
  mm->allocated += size;
  ADJUST ();
  return result;
}

void *
btor_realloc (BtorMemMgr *mm, void *p, size_t old_size, size_t new_size)
{
  void *result;
  assert (mm != NULL);
  assert (!p == !old_size);
  assert (mm->allocated >= old_size);
  result = realloc (p, new_size);
  BTOR_ABORT_MEM (result == NULL, "out of memory in 'btor_realloc'");
  mm->allocated -= old_size;
  mm->allocated += new_size;
  ADJUST ();
  return result;
}

void *
btor_calloc (BtorMemMgr *mm, size_t nobj, size_t size)
{
  void *result;
  assert (mm != NULL);
  result = calloc (nobj, size);
  BTOR_ABORT_MEM (result == NULL, "out of memory in 'btor_calloc'");
  mm->allocated += nobj * size;
  ADJUST ();
  return result;
}

void
btor_free (BtorMemMgr *mm, void *p, size_t freed)
{
  assert (mm != NULL);
  assert (!p == !freed);
  assert (mm->allocated >= freed);
  mm->allocated -= freed;
  free (p);
}

char *
btor_strdup (BtorMemMgr *mm, const char *str)
{
  char *res;

  if (str)
  {
    res = btor_malloc (mm, strlen (str) + 1);
    ADJUST ();
    strcpy (res, str);
  }
  else
    res = 0;

  return res;
}

void
btor_freestr (BtorMemMgr *mm, char *str)
{
  if (str) btor_free (mm, str, strlen (str) + 1);
}

void
btor_delete_mem_mgr (BtorMemMgr *mm)
{
  assert (mm != NULL);
  assert (getenv ("BTORLEAKMEM") || mm->allocated == 0);
  free (mm);
}

size_t
btor_parse_error_message_length (const char *name, const char *fmt, va_list ap)
{
  size_t bytes = strlen (name) + 20; /* care for ':: \0' and lineno */
  const char *p;

  for (p = fmt; *p; p++)
  {
    if (*p == '%')
    {
      p++;
      assert (*p);
      if (*p == 'c')
      {
        (void) va_arg (ap, int);
        bytes += 1;
      }
      else if (*p == 'd' || *p == 'u')
      {
        (void) va_arg (ap, unsigned);
        bytes += 12;
      }
      else
      {
        assert (*p == 's');
        bytes += strlen (va_arg (ap, const char *));
      }
    }
    else
      bytes++;
  }

  return bytes;
}

char *
btor_parse_error_message (BtorMemMgr *mem,
                          const char *name,
                          int lineno,
                          const char *fmt,
                          va_list ap,
                          size_t bytes)
{
  char *res;
  char *tmp;

  tmp = btor_malloc (mem, bytes);
  sprintf (tmp, "%s:%d: ", name, lineno);
  assert (strlen (tmp) + 1 < bytes);
  vsprintf (tmp + strlen (tmp), fmt, ap);
  res = btor_strdup (mem, tmp);
  btor_free (mem, tmp, bytes);

  return res;
}

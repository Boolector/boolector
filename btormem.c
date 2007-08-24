#include "btormem.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

BtorMemMgr *
btor_new_mem_mgr (void)
{
  BtorMemMgr *mm = (BtorMemMgr *) malloc (sizeof (BtorMemMgr));
  mm->allocated  = 0;
  return mm;
}

void *
btor_malloc (BtorMemMgr *mm, size_t size)
{
  assert (mm != NULL);
  mm->allocated += size;
  return malloc (size);
}

void *
btor_realloc (BtorMemMgr *mm, void *p, size_t old_size, size_t new_size)
{
  assert (mm != NULL);
  assert (!p == !old_size);
  assert (mm->allocated >= old_size);
  mm->allocated -= old_size;
  mm->allocated += new_size;
  return realloc (p, new_size);
}

void *
btor_calloc (BtorMemMgr *mm, size_t nobj, size_t size)
{
  assert (mm != NULL);
  mm->allocated += nobj * size;
  return calloc (nobj, size);
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

char *
btor_parse_error_message (
    BtorMemMgr *mem, const char *name, int lineno, const char *fmt, va_list ap)

{
  const char *p;
  size_t bytes;
  char *res;
  char *tmp;

  bytes = strlen (name) + 20; /* care for ':: \0' and lineno */

  for (p = fmt; *p; p++)
  {
    if (*p == '%')
    {
      p++;
      assert (*p);
      if (*p == 'd' || *p == 'u')
        bytes += 12;
      else
      {
        assert (*p == 's');
        bytes += strlen (va_arg (ap, const char *));
      }
    }
    else
      bytes++;
  }

  tmp = btor_malloc (mem, bytes);
  sprintf (tmp, "%s:%d: ", name, lineno);
  assert (strlen (tmp) + 1 < bytes);
  vsprintf (tmp + strlen (tmp), fmt, ap);
  res = btor_strdup (mem, tmp);
  btor_free (mem, tmp, bytes);

  return res;
}

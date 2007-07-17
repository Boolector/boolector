#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "btormem.h"

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

/**
 *  BtorFMT: A tool package for the BTOR format.
 *
 *  Copyright (c) 2018 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of the BtorFMT package.
 *  See LICENSE.txt for more information on using this software.
 */

#ifndef BTORSIMMEM_H_INCLUDED
#define BTORSIMMEM_H_INCLUDED

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#define BTORSIM_NEWN(ptr, nelems) \
  ((ptr) = (typeof(ptr)) btorsim_malloc ((nelems) * sizeof *(ptr)))

#define BTORSIM_CNEWN(ptr, nelems) \
  ((ptr) = (typeof(ptr)) btorsim_calloc ((nelems), sizeof *(ptr)))

#define BTORSIM_CLRN(ptr, nelems) (memset ((ptr), 0, (nelems) * sizeof *(ptr)))

#define BTORSIM_REALLOC(p, n) \
  ((p) = (typeof(p)) btorsim_realloc ((p), ((n) * sizeof *(p))))

#define BTORSIM_NEW(ptr) BTORSIM_NEWN ((ptr), 1)

#define BTORSIM_CNEW(ptr) BTORSIM_CNEWN ((ptr), 1)

#define BTORSIM_CLR(ptr) BTORSIM_CLRN ((ptr), 1)

#define BTORSIM_DELETE(ptr) (free (ptr))

static inline void *
btorsim_malloc (size_t size)
{
  void *res;
  if (!size) return 0;
  res = malloc (size);
  if (!res)
  {
    fprintf (stderr, "[btorsim] memory allocation failed\n");
    abort ();
  }
  return res;
}

static inline void *
btorsim_calloc (size_t nobj, size_t size)
{
  void *res;
  res = calloc (nobj, size);
  if (!res)
  {
    fprintf (stderr, "[btorsim] memory allocation failed\n");
    abort ();
  }
  return res;
}

static inline void *
btorsim_realloc (void *p, size_t new_size)
{
  void *res;
  res = realloc (p, new_size);
  if (!res)
  {
    fprintf (stderr, "[btorsim] memory allocation failed\n");
    abort ();
  }
  return res;
}

static inline char *
btorsim_strdup (const char *str)
{
  char *res = 0;
  if (str)
  {
    BTORSIM_NEWN (res, strlen (str) + 1);
    strcpy (res, str);
  }
  return res;
}

#endif

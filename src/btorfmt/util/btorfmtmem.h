/**
 *  BtorFMT: A tool package for the BTOR format.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (c) 2018 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of the BtorFMT package.
 *  See LICENSE.txt for more information on using this software.
 */

#ifndef BTORFMTMEM_H_INCLUDED
#define BTORFMTMEM_H_INCLUDED

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#define BTORFMT_NEWN(ptr, nelems) \
  ((ptr) = (typeof(ptr)) btorsim_malloc ((nelems) * sizeof *(ptr)))

#define BTORFMT_CNEWN(ptr, nelems) \
  ((ptr) = (typeof(ptr)) btorsim_calloc ((nelems), sizeof *(ptr)))

#define BTORFMT_CLRN(ptr, nelems) (memset ((ptr), 0, (nelems) * sizeof *(ptr)))

#define BTORFMT_REALLOC(p, n) \
  ((p) = (typeof(p)) btorsim_realloc ((p), ((n) * sizeof *(p))))

#define BTORFMT_NEW(ptr) BTORFMT_NEWN ((ptr), 1)

#define BTORFMT_CNEW(ptr) BTORFMT_CNEWN ((ptr), 1)

#define BTORFMT_CLR(ptr) BTORFMT_CLRN ((ptr), 1)

#define BTORFMT_DELETE(ptr) (free (ptr))

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
    BTORFMT_NEWN (res, strlen (str) + 1);
    strcpy (res, str);
  }
  return res;
}

#endif

#include "boolector.h"
#include "btoropt.h"

#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void
die (const char *fmt, ...)
{
  va_list ap;
  va_start (ap, fmt);
  fprintf (stderr, "*** memcpy: ");
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static int
isint (const char *str)
{
  char ch;

  if ((ch = *str++) == '-') ch = *str++;

  if (!isdigit (ch)) return 0;

  while (isdigit ((ch = *str++)))
    ;

  return !ch;
}

int
main (int argc, char **argv)
{
  BoolectorNode *src, *dst, *eos, *eod, *p, *q, *tmp, *n, *j, *zero, *one;
  BoolectorNode *mem, *assumption, *alternative, *cmp, *root, *v;
  int i, len, havelen, overlapping, signed_size_t;
  BoolectorNode *old, *new;
  BoolectorSort isort, esort, asort;
  Btor *btor;

  len           = 0;
  havelen       = 0;
  overlapping   = 0;
  signed_size_t = 0;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: memcpy [-h][-o][-s] <len>\n");
      fprintf (stderr, "\n");
      fprintf (stderr, "  -h  print this command line option summary\n");
      fprintf (stderr, "  -o  allow 'src' and 'dst' to overlap\n");
      fprintf (stderr, "  -s  assume 'size_t' to be signed\n");
      exit (1);
    }
    else if (!strcmp (argv[i], "-o"))
    {
      overlapping = 1;
    }
    else if (!strcmp (argv[i], "-s"))
    {
      signed_size_t = 1;
    }
    else if (argv[i][0] == '-')
      die ("invalid command line option '%s'", argv[i]);
    else if (!isint (argv[i]))
      die ("expected integer but got '%s'", argv[i]);
    else if (havelen)
      die ("multiple integer arguments");
    else
    {
      havelen = 1;
      len     = atoi (argv[i]);
    }
  }

  if (!havelen) die ("length argument missing");

  if (len < 0 && !signed_size_t)
    die ("negative <len> while 'size_t' is unsigned (try '-s')");

  btor = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);

  isort = boolector_bitvec_sort (btor, 32);
  esort = boolector_bitvec_sort (btor, 8);
  asort = boolector_array_sort (btor, isort, esort);
  mem   = boolector_array (btor, asort, "mem");

  src = boolector_var (btor, isort, "src");
  dst = boolector_var (btor, isort, "dst");

  n = boolector_unsigned_int (btor, len, isort);

  j = boolector_var (btor, isort, "j");

  zero = boolector_zero (btor, isort);
  one  = boolector_one (btor, isort);

  eos = boolector_add (btor, src, n);
  eod = boolector_add (btor, dst, n);

  cmp        = boolector_ulte (btor, src, eos);
  assumption = cmp;

  cmp = boolector_ulte (btor, dst, eod);
  tmp = boolector_and (btor, assumption, cmp);
  boolector_release (btor, assumption);
  boolector_release (btor, cmp);
  assumption = tmp;

  if (!overlapping)
  {
    cmp         = boolector_ulte (btor, eos, dst);
    alternative = cmp;

    cmp = boolector_ulte (btor, eod, src);
    tmp = boolector_or (btor, alternative, cmp);
    boolector_release (btor, alternative);
    boolector_release (btor, cmp);
    alternative = tmp;

    tmp = boolector_and (btor, assumption, alternative);
    boolector_release (btor, assumption);
    boolector_release (btor, alternative);
    assumption = tmp;
  }

  if (signed_size_t)
  {
    cmp = boolector_slte (btor, zero, j);
    tmp = boolector_and (btor, assumption, cmp);
    boolector_release (btor, assumption);
    boolector_release (btor, cmp);
    assumption = tmp;
  }

  if (signed_size_t)
    cmp = boolector_slt (btor, j, n);
  else
    cmp = boolector_ult (btor, j, n);

  tmp = boolector_and (btor, assumption, cmp);
  boolector_release (btor, assumption);
  boolector_release (btor, cmp);
  assumption = tmp;

  p   = boolector_add (btor, src, j);
  old = boolector_read (btor, mem, p);
  boolector_release (btor, p);

  p = boolector_copy (btor, src);
  q = boolector_copy (btor, dst);

  for (i = 0; i < len; i++)
  {
    v   = boolector_read (btor, mem, p);
    tmp = boolector_write (btor, mem, q, v);
    boolector_release (btor, mem);
    boolector_release (btor, v);
    mem = tmp;

    tmp = boolector_add (btor, p, one);
    boolector_release (btor, p);
    p = tmp;

    tmp = boolector_add (btor, q, one);
    boolector_release (btor, q);
    q = tmp;
  }

  boolector_release (btor, q);
  q   = boolector_add (btor, dst, j);
  new = boolector_read (btor, mem, q);

  cmp = boolector_ne (btor, old, new);

  root = boolector_and (btor, assumption, cmp);
  boolector_release (btor, assumption);
  boolector_release (btor, cmp);

  boolector_dump_btor_node (btor, stdout, root);

  boolector_release (btor, root);
  boolector_release (btor, p);
  boolector_release (btor, q);
  boolector_release (btor, old);
  boolector_release (btor, new);
  boolector_release (btor, eos);
  boolector_release (btor, eod);
  boolector_release (btor, one);
  boolector_release (btor, zero);
  boolector_release (btor, j);
  boolector_release (btor, n);
  boolector_release (btor, dst);
  boolector_release (btor, src);
  boolector_release (btor, mem);
  boolector_release_sort (btor, isort);
  boolector_release_sort (btor, esort);
  boolector_release_sort (btor, asort);
  boolector_delete (btor);

  return 0;
}

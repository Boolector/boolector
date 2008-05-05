#include "../../boolector.h"

#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void
die (const char* fmt, ...)
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
isint (const char* str)
{
  char ch;

  if ((ch = *str++) == '-') ch = *str++;

  if (!isdigit (ch)) return 0;

  while (isdigit ((ch = *str++)))
    ;

  return !ch;
}

int
main (int argc, char** argv)
{
  BtorExp *src, *dst, *eos, *eod, *p, *q, *tmp, *n, *j, *zero, *one;
  BtorExp *mem, *assumption, *alternative, *cmp, *root, *v;
  int i, len, havelen, overlapping, signed_size_t;
  BtorExp *old, *new;
  Btor* btor;

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
    else if (!argv[i][0] == '-')
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

  btor = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);

  mem = btor_array_exp (btor, 8, 32);

  src = btor_var_exp (btor, 32, "src");
  dst = btor_var_exp (btor, 32, "dst");

  n = btor_unsigned_to_exp (btor, len, 32);

  j = btor_var_exp (btor, 32, "j");

  zero = btor_zero_exp (btor, 32);
  one  = btor_one_exp (btor, 32);

  eos = btor_add_exp (btor, src, n);
  eod = btor_add_exp (btor, dst, n);

  cmp        = btor_ulte_exp (btor, src, eos);
  assumption = cmp;

  cmp = btor_ulte_exp (btor, dst, eod);
  tmp = btor_and_exp (btor, assumption, cmp);
  btor_release_exp (btor, assumption);
  btor_release_exp (btor, cmp);
  assumption = tmp;

  if (!overlapping)
  {
    cmp         = btor_ulte_exp (btor, eos, dst);
    alternative = cmp;

    cmp = btor_ulte_exp (btor, eod, src);
    tmp = btor_or_exp (btor, alternative, cmp);
    btor_release_exp (btor, alternative);
    btor_release_exp (btor, cmp);
    alternative = tmp;

    tmp = btor_and_exp (btor, assumption, alternative);
    btor_release_exp (btor, assumption);
    btor_release_exp (btor, alternative);
    assumption = tmp;
  }

  if (signed_size_t)
  {
    cmp = btor_slte_exp (btor, zero, j);
    tmp = btor_and_exp (btor, assumption, cmp);
    btor_release_exp (btor, assumption);
    btor_release_exp (btor, cmp);
    assumption = tmp;
  }

  if (signed_size_t)
    cmp = btor_slt_exp (btor, j, n);
  else
    cmp = btor_ult_exp (btor, j, n);

  tmp = btor_and_exp (btor, assumption, cmp);
  btor_release_exp (btor, assumption);
  btor_release_exp (btor, cmp);
  assumption = tmp;

  p   = btor_add_exp (btor, src, j);
  old = btor_read_exp (btor, mem, p);
  btor_release_exp (btor, p);

  p = btor_copy_exp (btor, src);
  q = btor_copy_exp (btor, dst);

  for (i = 0; i < len; i++)
  {
    v   = btor_read_exp (btor, mem, p);
    tmp = btor_write_exp (btor, mem, q, v);
    btor_release_exp (btor, mem);
    btor_release_exp (btor, v);
    mem = tmp;

    tmp = btor_add_exp (btor, p, one);
    btor_release_exp (btor, p);
    p = tmp;

    tmp = btor_add_exp (btor, q, one);
    btor_release_exp (btor, q);
    q = tmp;
  }

  btor_release_exp (btor, q);
  q   = btor_add_exp (btor, dst, j);
  new = btor_read_exp (btor, mem, q);

  cmp = btor_ne_exp (btor, old, new);

  root = btor_and_exp (btor, assumption, cmp);
  btor_release_exp (btor, assumption);
  btor_release_exp (btor, cmp);

  btor_dump_exp (btor, stdout, root);

  btor_release_exp (btor, root);
  btor_release_exp (btor, p);
  btor_release_exp (btor, q);
  btor_release_exp (btor, old);
  btor_release_exp (btor, new);
  btor_release_exp (btor, eos);
  btor_release_exp (btor, eod);
  btor_release_exp (btor, one);
  btor_release_exp (btor, zero);
  btor_release_exp (btor, j);
  btor_release_exp (btor, n);
  btor_release_exp (btor, dst);
  btor_release_exp (btor, src);
  btor_release_exp (btor, mem);
  btor_delete_btor (btor);

  return 0;
}

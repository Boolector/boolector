#include "../../boolector.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void
die (const char* fmt, ...)
{
  va_list ap;
  fputs ("*** genreverse: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static int
isnum (const char* str)
{
  char ch;

  ch = *str++;

  if (!isdigit (ch)) return 0;

  while (isdigit ((ch = *str++)))
    ;

  return !ch;
}

int
main (int argc, char** argv)
{
  BtorExp *registers, *memory, *initial, *root, *prev, *current, *next;
  BtorExp *zero, *tmp, *assumption, *currentval;
  int i, len = -1;
  Btor* btor;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: reverse [-h] <len>\n");
      exit (1);
    }
    else if (argv[i][0] == '-' && isnum (argv[i] + 1))
      die ("negative length argument");
    else if (argv[i][0] == '-')
      die ("invalid command line option '%s'", argv[i]);
    else if (len >= 0)
      die ("too many arguments");
    else if (!isnum (argv[i]))
      die ("expected length argument but got '%s'", argv[i]);
    else
    {
      len = atoi (argv[i]);
      assert (len >= 0);
    }
  }

  if (len < 0) die ("length argument missing");

  btor = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);

  registers = btor_array_exp (btor, 32, 2);
  memory    = btor_array_exp (btor, 32, 30);

  initial = btor_copy_exp (btor, memory);

  prev    = btor_unsigned_to_exp (btor, 0, 2);
  current = btor_unsigned_to_exp (btor, 1, 2);
  next    = btor_unsigned_to_exp (btor, 2, 2);

  zero = btor_zeros_exp (btor, 32);

  root = btor_true_exp (btor);

  {
    tmp = btor_write_exp (btor, registers, prev, zero);
    btor_release_exp (btor, registers);
    registers = tmp;
  }

  for (i = 0; i < len; i++)
  {
    currentval = btor_read_exp (btor, registers, current);
    assumption = btor_ne_exp (btor, currentval, zero);
    btor_release_exp (btor, currentval);
    tmp = btor_and_exp (btor, root, assumption);
    btor_release_exp (btor, root);
    root = tmp;
    btor_release_exp (btor, assumption);
  }

  btor_release_exp (btor, registers);
  btor_release_exp (btor, initial);
  btor_release_exp (btor, memory);
  btor_release_exp (btor, prev);
  btor_release_exp (btor, next);
  btor_release_exp (btor, current);
  btor_release_exp (btor, zero);

  btor_dump_exp (btor, stdout, root);
  btor_release_exp (btor, root);

  btor_delete_btor (btor);

  return 0;
}

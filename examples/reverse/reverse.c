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
  int i, len = -1;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: reverse [-h] <len>\n");
      exit (1);
    }
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

  return 0;
}

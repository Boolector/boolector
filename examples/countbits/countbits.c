/* Verifies correcntess of Peter Wegner's algorithm:
 *
 *   P. Wegner.
 *   A technique for counting ones in a binary computer.
 *   CACM 3(5), 1960.
 *
 *  The algorithm goes as follows:
 *
 *    for (y = x, c = 0; y; y &= y - 1)
 *      c++;
 *
 *  We unroll this bit witdh (n) times
 *
 *    for (c = i = 0; i < n; i++, y &= y - 1)
 *      if (y)
 *        c++;
 *
 *  and compare it against
 *
 *    for (s = i = 0; i < n; i++)
 *      if (x & (1 << i))
 *        s++;
 *
 *  then 's = c'.
 */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void
die (const char* fmt, ...)
{
  va_list ap;
  fputs ("*** countbits: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

int
main (int argc, char** argv)
{
  int i, j, n = -1, x, y, c, tmp, s;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: countbits -h | <bits>\n");
      exit (0);
    }
    else if (argv[i][0] == '-')
      die ("unsupported command line option '%s'", argv[i]);
    else if (n >= 0)
      die ("more than one argument");
    else if ((n = atoi (argv[i])) <= 1)
      die ("number bits has to be larger than one");
  }

  if (n < 0) die ("number of bits missing");

  tmp = 1;

  printf ("1 var %d\n", n);
  x = y = 1;

  printf ("2 const %d ", n);

  for (j = 1; j < n; j++) fputc ('0', stdout);

  fputs ("1\n", stdout);

  printf ("3 zero %d\n", n);
  c = s = 3;

  tmp = 4;

  for (i = 0; i < n; i++)
  {
    if (i < n - 1)
    {
      printf ("%d sub %d %d 2\n", tmp, n, y);
      tmp++;

      printf ("%d and %d %d %d\n", tmp, n, y, tmp - 1);
      tmp++;
    }

    if (i)
    {
      printf ("%d add %d %d 2\n", tmp, n, c);
      tmp++;
    }

    printf ("%d redor 1 %d\n", tmp, y);
    tmp++;

    y = i ? tmp - 3 : tmp - 2;

    printf ("%d cond %d %d %d %d\n", tmp, n, tmp - 1, i ? tmp - 2 : 2, c);
    c = tmp++;

    if (i)
    {
      printf ("%d add %d %d 2\n", tmp, n, s);
      tmp++;
    }

    printf ("%d slice 1 %d %d %d\n", tmp, x, i, i);
    tmp++;

    printf ("%d cond %d %d %d %d\n", tmp, n, tmp - 1, i ? tmp - 2 : 2, s);
    s = tmp++;
  }

  printf ("%d eq 1 %d %d\n", tmp, c, s);
  tmp++;

  printf ("%d root 1 %d\n", tmp, -(tmp - 1));
  tmp++;

  return 0;
}

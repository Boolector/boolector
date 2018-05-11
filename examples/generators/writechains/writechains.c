#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int
isnum (const char *str)
{
  const char *p;
  for (p = str; *p; p++)
    if (!isdigit (*p)) return 0;
  return 1;
}

int
main (int argc, char **argv)
{
  int i, j, n = -1, *v, first, second, idx, c[4], aligned = 0, assumption;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-a"))
    {
      if (aligned)
      {
        fprintf (stderr, "*** writechains: multiple '-a' options\n");
        exit (1);
      }

      aligned = 1;
    }
    else if (isnum (argv[i]))
    {
      if (n >= 0)
      {
        fprintf (stderr, "*** writechains: multiple <length> arguments\n");
        exit (1);
      }

      n = atoi (argv[i]);
    }
    else
    {
      fprintf (stderr, "*** usage: writechains [-a] <length>\n");
      exit (1);
    }
  }

  if (n < 0)
  {
    fprintf (stderr, "*** writechains: <length> argument missing\n");
    exit (1);
  }

  first = second = idx = 1;
  printf ("%d array 8 32\n", idx++);
  v = malloc (n * sizeof *v);

  for (i = 0; i < 4; i++) printf ("%d constd 32 %d\n", c[i] = idx++, i);

  for (i = 0; i < n; i++) printf ("%d var 32\n", v[i] = idx++);

  for (i = 0; i < n; i++)
  {
    for (j = 0; j < 32; j += 8)
    {
      printf ("%d add 32 %d %d\n", idx++, v[i], c[j / 8]);
      printf ("%d slice 8 %d %d %d\n", idx++, v[i], j + 7, j);
      printf ("%d write 8 32 %d %d %d\n", idx, first, idx - 2, idx - 1);
      first = idx++;
    }
  }

  for (i = n - 1; i >= 0; i--)
  {
    for (j = 0; j < 32; j += 8)
    {
      printf ("%d add 32 %d %d\n", idx++, v[i], c[j / 8]);
      printf ("%d slice 8 %d %d %d\n", idx++, v[i], j + 7, j);
      printf ("%d write 8 32 %d %d %d\n", idx, second, idx - 2, idx - 1);
      second = idx++;
    }
  }

  assumption = -idx;
  printf ("%d eq 1 %d %d\n", idx++, first, second);

  if (aligned)
  {
    for (i = 0; i < n; i++)
    {
      printf ("%d slice 2 %d 1 0\n", idx++, v[i]);
      printf ("%d redor 1 %d\n", idx, idx - 1);
      idx++;
      printf ("%d and 1 %d %d\n", idx, assumption, -(idx - 1));
      assumption = idx++;
    }
  }

  printf ("%d root 1 %d\n", idx++, assumption);

  free (v);

  return 0;
}

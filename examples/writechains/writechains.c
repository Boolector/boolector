#include <stdio.h>
#include <stdlib.h>

int
main (int argc, char** argv)
{
  int i, l, n;

  if (argc != 2 || (l = atoi (argv[1])) <= 0)
  {
    fprintf (stderr, "*** usage: writechains <bits>\n");
    exit (1);
  }

  n = (1 << l);

  printf ("1 array %d %d\n", l, l);

  for (i = 0; i < n; i++)
#if 0
    printf ("%d constd %d %d\n", i + 2, l, i);
#else
    printf ("%d var %d\n", i + 2, l);
#endif

    for (i = 0; i < n; i++)
      printf ("%d write %d %d %d %d\n",
              n + 2 + i,
              l,
              i ? n + 1 + i : 1,
              i + 2,
              i + 2);

  for (i = 0; i < n; i++)
    printf ("%d write %d %d %d %d\n",
            2 * n + 2 + i,
            l,
            i ? 2 * n + 1 + i : 1,
            n - i + 1,
            n - i + 1);

  printf ("%d eq 1 %d %d\n", 3 * n + 2, 2 * n + 1, 3 * n + 1);
  printf ("%d root 1 -%d\n", 3 * n + 3, 3 * n + 2);

  return 0;
}

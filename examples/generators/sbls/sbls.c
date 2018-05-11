#include <stdio.h>
#include <stdlib.h>

int
main (int argc, char** argv)
{
  int n = argc > 1 ? atoi (argv[1]) : 2, i, j, k, w, po2;
  printf ("; spatially-balanced latin squares\n");
  w = 1;
  while ((1 << w) < n) w++;
  po2 = ((1 << w) == n);
  printf ("; n = %d, w = %d\n", n, w);
  printf ("(set-logic QF_BV)\n");
  if (!po2)
  {
    printf ("(declare-fun n () (_ BitVec %d))\n", w);
    printf ("(assert (= n (_ bv%d %d)))\n", n, w);
  }
  for (i = 0; i < n; i++)
    for (j = 0; j < n; j++)
    {
      printf ("(declare-fun r%dc%d () (_ BitVec %d))\n", i, j, w);
      if (!po2) printf ("(assert (bvult r%dc%d n))\n", i, j);
    }
  for (i = 0; i < n; i++)
    for (j = 0; j < n - 1; j++)
      for (k = j + 1; k < n; k++)
      {
        printf ("(assert (distinct r%dc%d r%dc%d))\n", i, j, i, k);
        printf ("(assert (distinct r%dc%d r%dc%d))\n", j, i, k, i);
      }
  printf ("(check-sat)\n");
  printf ("(exit)\n");
  return 0;
}

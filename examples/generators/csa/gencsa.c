#include <stdio.h>
#include <stdlib.h>

int
main (int argc, char** argv)
{
  int n, w, i;
  if (argc != 3 || (n = atoi (argv[1])) < 2 || (w = atoi (argv[2])) < 2)
  {
    fprintf (stderr,
             "usage: gensat addends bit-width (addends, bitwidth > 1)\n");
    exit (1);
  }
  printf ("(set-logic QF_BV)\n");
  for (i = 0; i < n; i++) printf ("(declare-fun a%d () (_ BitVec %d))\n", i, w);
  printf ("(declare-fun x () (_ BitVec %d))\n", w);
  printf ("(assert (= x");
  for (i = 0; i < n - 1; i++) printf (" (bvadd a%d", i);
  printf (" a%d", i);
  while (i-- > 0) printf (")");
  printf ("))\n");
  printf ("(declare-fun s0 () (_ BitVec %d))\n", w);
  printf ("(declare-fun c0 () (_ BitVec %d))\n", w);
  printf ("(declare-fun d0 () (_ BitVec %d))\n", w);
  printf ("(assert (= s0 (bvxor a0 a1)))\n");
  printf ("(assert (= c0 (bvand a0 a1)))\n");
  printf ("(assert (= d0 (concat ((_ extract %d 0) c0) (_ bv0 1))))\n", w - 2);
  for (i = 1; i < n - 1; i++)
  {
    printf ("(declare-fun s%d () (_ BitVec %d))\n", i, w);
    printf ("(declare-fun c%d () (_ BitVec %d))\n", i, w);
    printf ("(declare-fun d%d () (_ BitVec %d))\n", i, w);
    printf ("(assert (= s%d (bvxor s%d (bvxor d%d a%d))))\n",
            i,
            i - 1,
            i - 1,
            i + 1);
    printf (
        "(assert (= c%d (bvor (bvand s%d d%d) (bvor (bvand s%d a%d) (bvand d%d "
        "a%d)))))\n",
        i,
        i - 1,
        i - 1,
        i - 1,
        i + 1,
        i - 1,
        i + 1);
    printf ("(assert (= d%d (concat ((_ extract %d 0) c%d) (_ bv0 1))))\n",
            i,
            w - 2,
            i);
  }
  printf ("(declare-fun y () (_ BitVec %d))\n", w);
  printf ("(assert (= y (bvadd s%d d%d)))\n", n - 2, n - 2);
  printf ("(assert (distinct x y))\n");
  printf ("(check-sat)\n");
  printf ("(exit)\n");
  exit (0);
}

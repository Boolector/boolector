#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int
main (int argc, char** argv)
{
  int d = -1, td, w, i, sat = 0;
  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      printf ("usage: pjex [-h][-s|--sat] <num-bits>\n");
      exit (0);
    }
    if (!strcmp (argv[i], "-s") || !strcmp (argv[i], "--sat"))
      sat = 1;
    else if (argv[i][0] == '-')
    {
      fprintf (stderr, "*** pjex: invalid option '%s'\n", argv[i]);
      printf ("usage: pjex [-h][-s|--sat] <num-bits>\n");
      exit (1);
    }
    else if (d > 0)
    {
      fprintf (stderr, "*** pjex: multiple '<num-bits>' options\n");
      printf ("usage: pjex [-h][-s|--sat] <num-bits>\n");
      exit (1);
    }
    else if ((d = atoi (argv[i])) <= 1)
    {
      fprintf (stderr, "*** pjex: argument '%s' invalid\n", argv[i]);
      printf ("usage: pjex [-h][-s|--sat] <num-bits>\n");
      exit (1);
    }
  }
  if (d < 0)
  {
    fprintf (stderr, "*** pjex: argument missing\n");
    printf ("usage: pjex [-h][-s|--sat] <num-bits>\n");
    exit (1);
  }
  printf ("; Pete Jeavons Example CSP example\n");
  td = 2 * d;
  w  = 1;
  while ((1 << (w - 1)) <= d) w++;
  printf ("; d = %d, 2d = %d, w = %d\n", d, td, w);

  printf ("(set-logic QF_BV)\n");
  printf ("(declare-fun lb () (_ BitVec %d))\n", w);
  printf ("(declare-fun ub () (_ BitVec %d))\n", w);
  for (i = 1; i <= td; i++)
    printf ("(declare-fun x1a%d () (_ BitVec %d))\n", i, w),
        printf ("(declare-fun x2a%d () (_ BitVec %d))\n", i, w);

  printf ("(assert (= lb (_ bv1 %d)))\n", w);
  printf ("(assert (= ub (_ bv%d %d)))\n", d, w);

  for (i = 1; i <= td; i++)
    printf ("(assert (and (bvule lb x1a%d) (bvule x1a%d ub)))\n", i, i),
        printf ("(assert (and (bvule lb x2a%d) (bvule x2a%d ub)))\n", i, i);

  for (i = 1; i < td; i++)
  {
    if (i == td - 1 && sat) printf (";");
    printf ("(assert (bvult (bvadd x1a%d x2a%d) (bvadd x1a%d x2a%d)))\n",
            i,
            i,
            i + 1,
            i + 1);
  }

  printf ("(check-sat)\n");
  printf ("(exit)\n");

  return 0;
}

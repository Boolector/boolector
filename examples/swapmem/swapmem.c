#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "boolector.h"
#include "btoropt.h"

static BoolectorNode *
swap_with_xor (Btor *btor,
               BoolectorNode *mem,
               int num_elements,
               BoolectorNode *start1,
               BoolectorNode *start2)
{
  BoolectorSort s;
  BoolectorNode *x, *y, *result, *temp, *xor, *pos1, *pos2, *one;
  int i;
  assert (btor != NULL);
  assert (mem != NULL);
  assert (num_elements > 0);
  assert (start1 != NULL);
  assert (start2 != NULL);
  result = mem;
  pos1   = boolector_copy (btor, start1);
  pos2   = boolector_copy (btor, start2);
  s      = boolector_bitvec_sort (btor, 32);
  one    = boolector_one (btor, s);
  boolector_release_sort (btor, s);
  for (i = 0; i < num_elements; i++)
  {
    /* we can swap two elements without a temporay variable
     * by the following steps:
     * x ^= y
     * y ^= x
     * x ^= y
     */
    x    = boolector_read (btor, result, pos1);
    y    = boolector_read (btor, result, pos2);
    xor  = boolector_xor (btor, x, y);
    temp = boolector_write (btor, result, pos1, xor);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, x);
    boolector_release (btor, xor);

    x    = boolector_read (btor, result, pos1);
    xor  = boolector_xor (btor, x, y);
    temp = boolector_write (btor, result, pos2, xor);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, y);
    boolector_release (btor, xor);

    y    = boolector_read (btor, result, pos2);
    xor  = boolector_xor (btor, x, y);
    temp = boolector_write (btor, result, pos1, xor);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, x);
    boolector_release (btor, y);
    boolector_release (btor, xor);

    temp = boolector_add (btor, pos1, one);
    boolector_release (btor, pos1);
    pos1 = temp;

    temp = boolector_add (btor, pos2, one);
    boolector_release (btor, pos2);
    pos2 = temp;
  }
  boolector_release (btor, one);
  boolector_release (btor, pos1);
  boolector_release (btor, pos2);
  return result;
}

int
main (int argc, char **argv)
{
  int num_elements, overlap;
  Btor *btor;
  BoolectorSort isort, esort, asort;
  BoolectorNode *mem, *orig_mem, *formula, *start1, *start2, *num_elements_exp;
  BoolectorNode *add1, *add2, *ugte1, *ugte2, *temp, * or, *uaddo1, *uaddo2;
  BoolectorNode *not_uaddo1, *not_uaddo2, *premisse_part1, *premisse_part2;
  if ((argc != 2 && argc != 3)
      || (argc == 2
          && (strcmp (argv[1], "-h") == 0 || strcmp (argv[1], "--help") == 0))
      || (argc == 3 && strcmp (argv[2], "-o") != 0))
  {
    printf ("Usage: ./swapmem <num-elements> [-o]\n");
    return 1;
  }
  num_elements = atoi (argv[1]);
  if (num_elements <= 0)
  {
    printf ("Number of elements must be greater than zero\n");
    return 1;
  }

  if (argc == 3)
    overlap = 1;
  else
    overlap = 0;

  btor = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);

  esort = boolector_bitvec_sort (btor, 8);
  isort = boolector_bitvec_sort (btor, 32);
  asort = boolector_array_sort (btor, isort, esort);

  mem      = boolector_array (btor, asort, "mem");
  orig_mem = boolector_copy (btor, mem);
  start1   = boolector_var (btor, isort, "start1");
  start2   = boolector_var (btor, isort, "start2");
  mem      = swap_with_xor (btor, mem, num_elements, start1, start2);
  mem      = swap_with_xor (btor, mem, num_elements, start1, start2);
  /* memory has to be equal */
  /* we show this by showing that the negation is unsat */
  formula = boolector_eq (btor, mem, orig_mem);

  if (!overlap)
  {
    /* we do not allow that two locations overlap */
    num_elements_exp = boolector_unsigned_int (btor, num_elements, isort);

    add1       = boolector_add (btor, start1, num_elements_exp);
    ugte1      = boolector_ugte (btor, start2, add1);
    uaddo1     = boolector_uaddo (btor, start1, num_elements_exp);
    not_uaddo1 = boolector_not (btor, uaddo1);

    add2       = boolector_add (btor, start2, num_elements_exp);
    ugte2      = boolector_ugte (btor, start1, add2);
    uaddo2     = boolector_uaddo (btor, start2, num_elements_exp);
    not_uaddo2 = boolector_not (btor, uaddo2);

    premisse_part1 = boolector_and (btor, ugte1, not_uaddo1);
    temp           = boolector_and (btor, premisse_part1, not_uaddo2);
    boolector_release (btor, premisse_part1);
    premisse_part1 = temp;

    premisse_part2 = boolector_and (btor, ugte2, not_uaddo2);
    temp           = boolector_and (btor, premisse_part2, not_uaddo1);
    boolector_release (btor, premisse_part2);
    premisse_part2 = temp;

    or   = boolector_or (btor, premisse_part1, premisse_part2);
    temp = boolector_implies (btor, or, formula);
    boolector_release (btor, formula);
    formula = temp;

    boolector_release (btor, num_elements_exp);
    boolector_release (btor, ugte1);
    boolector_release (btor, ugte2);
    boolector_release (btor, add1);
    boolector_release (btor, add2);
    boolector_release (btor, or);
    boolector_release (btor, uaddo1);
    boolector_release (btor, uaddo2);
    boolector_release (btor, not_uaddo1);
    boolector_release (btor, not_uaddo2);
    boolector_release (btor, premisse_part1);
    boolector_release (btor, premisse_part2);
  }

  temp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = temp;
  boolector_dump_btor_node (btor, stdout, formula);
  /* clean up */
  boolector_release (btor, formula);
  boolector_release (btor, mem);
  boolector_release (btor, start1);
  boolector_release (btor, start2);
  boolector_release (btor, orig_mem);
  boolector_release_sort (btor, isort);
  boolector_release_sort (btor, esort);
  boolector_release_sort (btor, asort);
  boolector_delete (btor);
  return 0;
}

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../boolector.h"

static BtorExp *
swap_with_xor (Btor *btor,
               BtorExp *mem,
               int num_elements,
               BtorExp *start1,
               BtorExp *start2)
{
  BtorExp *x, *y, *result, *temp, *xor, *pos1, *pos2, *one;
  int i;
  assert (btor != NULL);
  assert (mem != NULL);
  assert (num_elements > 0);
  assert (start1 != NULL);
  assert (start2 != NULL);
  result = mem;
  pos1   = btor_copy_exp (btor, start1);
  pos2   = btor_copy_exp (btor, start2);
  one    = btor_one_exp (btor, 32);
  for (i = 0; i < num_elements; i++)
  {
    /* we can swap two elements without a temporay variable
     * by the following steps:
     * x ^= y
     * y ^= x
     * x ^= y
     */
    x    = btor_read_exp (btor, result, pos1);
    y    = btor_read_exp (btor, result, pos2);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, pos1, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, x);
    btor_release_exp (btor, xor);

    x    = btor_read_exp (btor, result, pos1);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, pos2, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, y);
    btor_release_exp (btor, xor);

    y    = btor_read_exp (btor, result, pos2);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, pos1, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, x);
    btor_release_exp (btor, y);
    btor_release_exp (btor, xor);

    temp = btor_add_exp (btor, pos1, one);
    btor_release_exp (btor, pos1);
    pos1 = temp;

    temp = btor_add_exp (btor, pos2, one);
    btor_release_exp (btor, pos2);
    pos2 = temp;
  }
  btor_release_exp (btor, one);
  btor_release_exp (btor, pos1);
  btor_release_exp (btor, pos2);
  return result;
}

int
main (int argc, char **argv)
{
  int num_elements, overlap;
  Btor *btor;
  BtorExp *mem, *orig_mem, *formula, *start1, *start2, *num_elements_exp;
  BtorExp *add1, *add2, *ugte1, *ugte2, *temp, * or, *uaddo1, *uaddo2;
  BtorExp *not_uaddo1, *not_uaddo2, *premisse_part1, *premisse_part2;
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

  btor = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);

  mem      = btor_array_exp (btor, 8, 32);
  orig_mem = btor_copy_exp (btor, mem);
  start1   = btor_var_exp (btor, 32, "start1");
  start2   = btor_var_exp (btor, 32, "start2");
  mem      = swap_with_xor (btor, mem, num_elements, start1, start2);
  mem      = swap_with_xor (btor, mem, num_elements, start1, start2);
  /* memory has to be equal */
  /* we show this by showing that the negation is unsat */
  formula = btor_eq_exp (btor, mem, orig_mem);

  if (!overlap)
  {
    /* we do not allow that two locations overlap */
    num_elements_exp = btor_unsigned_to_exp (btor, num_elements, 32);

    add1       = btor_add_exp (btor, start1, num_elements_exp);
    ugte1      = btor_ugte_exp (btor, start2, add1);
    uaddo1     = btor_uaddo_exp (btor, start1, num_elements_exp);
    not_uaddo1 = btor_not_exp (btor, uaddo1);

    add2       = btor_add_exp (btor, start2, num_elements_exp);
    ugte2      = btor_ugte_exp (btor, start1, add2);
    uaddo2     = btor_uaddo_exp (btor, start2, num_elements_exp);
    not_uaddo2 = btor_not_exp (btor, uaddo2);

    premisse_part1 = btor_and_exp (btor, ugte1, not_uaddo1);
    temp           = btor_and_exp (btor, premisse_part1, not_uaddo2);
    btor_release_exp (btor, premisse_part1);
    premisse_part1 = temp;

    premisse_part2 = btor_and_exp (btor, ugte2, not_uaddo2);
    temp           = btor_and_exp (btor, premisse_part2, not_uaddo1);
    btor_release_exp (btor, premisse_part2);
    premisse_part2 = temp;

    or   = btor_or_exp (btor, premisse_part1, premisse_part2);
    temp = btor_implies_exp (btor, or, formula);
    btor_release_exp (btor, formula);
    formula = temp;

    btor_release_exp (btor, num_elements_exp);
    btor_release_exp (btor, ugte1);
    btor_release_exp (btor, ugte2);
    btor_release_exp (btor, add1);
    btor_release_exp (btor, add2);
    btor_release_exp (btor, or);
    btor_release_exp (btor, uaddo1);
    btor_release_exp (btor, uaddo2);
    btor_release_exp (btor, not_uaddo1);
    btor_release_exp (btor, not_uaddo2);
    btor_release_exp (btor, premisse_part1);
    btor_release_exp (btor, premisse_part2);
  }

  temp = btor_not_exp (btor, formula);
  btor_release_exp (btor, formula);
  formula = temp;
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  btor_release_exp (btor, formula);
  btor_release_exp (btor, mem);
  btor_release_exp (btor, start1);
  btor_release_exp (btor, start2);
  btor_release_exp (btor, orig_mem);
  btor_delete_btor (btor);
  return 0;
}

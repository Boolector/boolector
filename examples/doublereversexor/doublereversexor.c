#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

static BtorExp *
reverse_with_xor (Btor *btor,
                  BtorExp *mem,
                  int num_elements,
                  BtorExp *orig_bottom_exp,
                  BtorExp *orig_top_exp)
{
  BtorExp *x, *y, *result, *temp, *xor, *bottom_exp, *top_exp, *one;
  int bottom;
  int top;
  assert (btor != NULL);
  assert (mem != NULL);
  assert (num_elements > 1);
  assert (orig_bottom_exp != NULL);
  assert (orig_top_exp != NULL);
  /* we reverse the array */
  result     = mem;
  bottom     = 0;
  top        = num_elements - 1;
  bottom_exp = btor_copy_exp (btor, orig_bottom_exp);
  top_exp    = btor_copy_exp (btor, orig_top_exp);
  one        = btor_one_exp (btor, 32);
  while (top > bottom)
  {
    /* we can swap two ints without a temporay variable
     * by the following steps:
     * x ^= y
     * y ^= x
     * x ^= y
     */
    x    = btor_read_exp (btor, result, bottom_exp);
    y    = btor_read_exp (btor, result, top_exp);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, bottom_exp, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, x);
    btor_release_exp (btor, xor);

    x    = btor_read_exp (btor, result, bottom_exp);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, top_exp, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, y);
    btor_release_exp (btor, xor);

    y    = btor_read_exp (btor, result, top_exp);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, bottom_exp, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, x);
    btor_release_exp (btor, y);
    btor_release_exp (btor, xor);

    top--;
    temp = btor_sub_exp (btor, top_exp, one);
    btor_release_exp (btor, top_exp);
    top_exp = temp;

    bottom++;
    temp = btor_add_exp (btor, bottom_exp, one);
    btor_release_exp (btor, bottom_exp);
    bottom_exp = temp;
  }
  btor_release_exp (btor, one);
  btor_release_exp (btor, bottom_exp);
  btor_release_exp (btor, top_exp);
  return result;
}

int
main (int argc, char **argv)
{
  int num_elements;
  Btor *btor;
  BtorExp *mem, *orig_mem, *formula, *top, *bottom;
  if (argc != 2)
  {
    printf ("Usage: ./doublereversexor <num-elements>\n");
    return 1;
  }
  num_elements = atoi (argv[1]);
  if (num_elements <= 1)
  {
    printf ("Number of elements must be greater than one\n");
    return 1;
  }

  btor = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);

  mem      = btor_array_exp (btor, 8, 32);
  orig_mem = btor_copy_exp (btor, mem);
  bottom   = btor_var_exp (btor, 32, "bottom");
  top      = btor_var_exp (btor, 32, "top");
  /* top and bottom can be arbitrary
   * if we reverse two times
   * we get the same memory as before
   * */
  mem = reverse_with_xor (btor, mem, num_elements, bottom, top);
  mem = reverse_with_xor (btor, mem, num_elements, bottom, top);
  /* memory has to be equal */
  /* we show this by showing that the negation is unsat */
  formula = btor_ne_exp (btor, mem, orig_mem);
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  btor_release_exp (btor, formula);
  btor_release_exp (btor, mem);
  btor_release_exp (btor, bottom);
  btor_release_exp (btor, top);
  btor_release_exp (btor, orig_mem);
  btor_delete_btor (btor);
  return 0;
}

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

BtorExp **indices;

static int
compute_num_bits_index (int num_elements)
{
  assert (num_elements > 1);
  while (!btor_is_power_of_2_util (num_elements)) num_elements++;
  return btor_log_2_util (num_elements);
}

static BtorExp *
reverse_array_with_xor (Btor *btor, BtorExp *array, int num_elements)
{
  BtorExp *x, *y, *result, *temp, *xor;
  int bottom;
  int top;
  assert (btor != NULL);
  assert (num_elements > 1);
  /* we reverse the array */
  result = array;
  bottom = 0;
  top    = num_elements - 1;
  while (top > bottom)
  {
    /* we can swap two ints without a temporay variable
     * by the following steps:
     * x ^= y
     * y ^= x
     * x ^= y
     */
    x    = btor_read_exp (btor, result, indices[bottom]);
    y    = btor_read_exp (btor, result, indices[top]);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, indices[bottom], xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, x);
    btor_release_exp (btor, xor);

    x    = btor_read_exp (btor, result, indices[bottom]);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, indices[top], xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, y);
    btor_release_exp (btor, xor);

    y    = btor_read_exp (btor, result, indices[top]);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, indices[bottom], xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, x);
    btor_release_exp (btor, y);
    btor_release_exp (btor, xor);
    top--;
    bottom++;
  }
  return result;
}

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i;
  Btor *btor;
  BtorExp *array, *orig_array, *formula;
  if (argc != 3)
  {
    printf ("Usage: ./genextdoublereversexor <num-bits> <num-elements>\n");
    return 1;
  }
  num_bits = atoi (argv[1]);
  if (num_bits <= 0)
  {
    printf ("Number of bits must be greater than zero\n");
    return 1;
  }
  num_elements = atoi (argv[2]);
  if (num_elements <= 1)
  {
    printf ("Number of elements must be greater than one\n");
    return 1;
  }
  num_bits_index = compute_num_bits_index (num_elements);
  btor           = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);
  indices = (BtorExp **) malloc (sizeof (BtorExp *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = btor_int_to_exp (btor, i, num_bits_index);
  array      = btor_array_exp (btor, num_bits, num_bits_index);
  orig_array = btor_copy_exp (btor, array);
  array      = reverse_array_with_xor (btor, array, num_elements);
  array      = reverse_array_with_xor (btor, array, num_elements);
  /* array has to be equal here, we reversed it two times */
  /* we show this by showing that the negation is unsat */
  formula = btor_ne_exp (btor, array, orig_array);
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (btor, indices[i]);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, array);
  btor_release_exp (btor, orig_array);
  btor_delete_btor (btor);
  free (indices);
  return 0;
}

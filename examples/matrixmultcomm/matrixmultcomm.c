#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

BtorNode **indices;

static BtorNode *
matrix_mult (Btor *btor,
             BtorNode *m1,
             BtorNode *m2,
             int size,
             int num_bits,
             int num_bits_index,
             const char *symbol)
{
  int i, j, k;
  BtorNode *temp, *result, *zero, *read1, *read2, *read3, *mult, *add;
  assert (btor != NULL);
  assert (m1 != NULL);
  assert (m2 != NULL);
  assert (size > 1);
  assert (num_bits >= 1);
  assert (num_bits_index >= 1);
  assert (symbol != NULL);
  result = boolector_array (btor, num_bits, num_bits_index, symbol);
  /* initialize result matrix with zeroes */
  zero = boolector_zero (btor, num_bits);
  for (i = 0; i < size * size; i++)
  {
    temp = boolector_write (btor, result, indices[i], zero);
    boolector_release (btor, result);
    result = temp;
  }
  boolector_release (btor, zero);
  /* matrix multiplication */
  for (i = 0; i < size; i++)
    for (j = 0; j < size; j++)
      for (k = 0; k < size; k++)
      {
        /* result[i][j] += m1[i][k] * m2[k][j]; */
        read1 = boolector_read (btor, result, indices[i * size + j]);
        read2 = boolector_read (btor, m1, indices[i * size + k]);
        read3 = boolector_read (btor, m2, indices[k * size + j]);
        mult  = boolector_mul (btor, read2, read3);
        add   = boolector_add (btor, read1, mult);
        temp  = boolector_write (btor, result, indices[i * size + j], add);
        boolector_release (btor, result);
        result = temp;
        boolector_release (btor, read1);
        boolector_release (btor, read2);
        boolector_release (btor, read3);
        boolector_release (btor, mult);
        boolector_release (btor, add);
      }
  return result;
}

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, size, i, num_elements;
  Btor *btor;
  BtorNode *A, *B, *A_x_B, *B_x_A, *formula, *temp;
  if (argc != 3)
  {
    printf ("Usage: ./matrixmultcomm <num-bits> <size>\n");
    return 1;
  }
  num_bits = atoi (argv[1]);
  if (num_bits <= 0)
  {
    printf ("Number of bits must be greater than zero\n");
    return 1;
  }
  size = atoi (argv[2]);
  if (size <= 1)
  {
    printf ("Size must be greater than one\n");
    return 1;
  }
  num_elements   = size * size;
  num_bits_index = btor_log_2_util (btor_next_power_of_2_util (num_elements));
  btor           = boolector_new ();
  boolector_set_opt_rewrite_level (btor, 0);
  indices = (BtorNode **) malloc (sizeof (BtorNode *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = boolector_int (btor, i, num_bits_index);
  A       = boolector_array (btor, num_bits, num_bits_index, "A");
  B       = boolector_array (btor, num_bits, num_bits_index, "B");
  A_x_B   = matrix_mult (btor, A, B, size, num_bits, num_bits_index, "AxB");
  B_x_A   = matrix_mult (btor, B, A, size, num_bits, num_bits_index, "BxA");
  formula = boolector_eq (btor, A_x_B, B_x_A);
  /* we negate the formula and try to show that it is unsatisfiable
   * formula is SAT as matrix multiplication is not commutative in general */
  temp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = temp;
  boolector_dump_btor (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) boolector_release (btor, indices[i]);
  boolector_release (btor, formula);
  boolector_release (btor, A);
  boolector_release (btor, B);
  boolector_release (btor, A_x_B);
  boolector_release (btor, B_x_A);
  boolector_delete (btor);
  free (indices);
  return 0;
}

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"
#include "btoropt.h"
#include "utils/btorutil.h"

BoolectorNode **indices;

static BoolectorNode *
matrix_mult (Btor *btor,
             BoolectorNode *m1,
             BoolectorNode *m2,
             int size,
             BoolectorSort esort,
             BoolectorSort asort,
             const char *symbol)
{
  int i, j, k;
  BoolectorNode *temp, *result, *zero, *read1, *read2, *read3, *mult, *add;
  assert (btor != NULL);
  assert (m1 != NULL);
  assert (m2 != NULL);
  assert (size > 1);
  assert (symbol != NULL);
  result = boolector_array (btor, asort, symbol);
  /* initialize result matrix with zeroes */
  zero = boolector_zero (btor, esort);
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
  BoolectorNode *A, *B, *C, *A_x_B, *B_x_C, *AB_x_C, *A_x_BC, *formula, *temp;
  BoolectorSort isort, esort, asort;
  if (argc != 3)
  {
    printf ("Usage: ./matrixmultass <num-bits> <size>\n");
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
  num_bits_index = btor_util_log_2 (btor_util_next_power_of_2 (num_elements));
  btor           = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
  indices = (BoolectorNode **) malloc (sizeof (BoolectorNode *) * num_elements);
  isort   = boolector_bitvec_sort (btor, num_bits_index);
  esort   = boolector_bitvec_sort (btor, num_bits);
  asort   = boolector_array_sort (btor, isort, esort);
  for (i = 0; i < num_elements; i++)
    indices[i] = boolector_int (btor, i, isort);
  A       = boolector_array (btor, asort, "A");
  B       = boolector_array (btor, asort, "B");
  C       = boolector_array (btor, asort, "C");
  A_x_B   = matrix_mult (btor, A, B, size, esort, asort, "AxB");
  B_x_C   = matrix_mult (btor, B, C, size, esort, asort, "BxC");
  AB_x_C  = matrix_mult (btor, A_x_B, C, size, esort, asort, "ABxC");
  A_x_BC  = matrix_mult (btor, A, B_x_C, size, esort, asort, "AxBC");
  formula = boolector_eq (btor, AB_x_C, A_x_BC);
  /* we negate the formula and try to show that it is unsatisfiable
   * if size is a power of 2, then the instance is UNSAT, else SAT */
  temp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = temp;
  boolector_dump_btor_node (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) boolector_release (btor, indices[i]);
  boolector_release (btor, formula);
  boolector_release (btor, A);
  boolector_release (btor, B);
  boolector_release (btor, C);
  boolector_release (btor, A_x_B);
  boolector_release (btor, B_x_C);
  boolector_release (btor, AB_x_C);
  boolector_release (btor, A_x_BC);
  boolector_release_sort (btor, isort);
  boolector_release_sort (btor, esort);
  boolector_release_sort (btor, asort);
  boolector_delete (btor);
  free (indices);
  return 0;
}

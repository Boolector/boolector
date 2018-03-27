#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"
#include "btoropt.h"
#include "utils/btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i;
  Btor *btor;
  BoolectorNode **indices, *array, *ugt, *temp, *read, *formula, *max, *index;
  BoolectorSort isort, esort, asort;
  if (argc != 3)
  {
    printf ("Usage: ./max <num-bits> <num-elements>\n");
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
  if (!btor_util_is_power_of_2 (num_elements))
  {
    printf ("Number of elements must be a power of two\n");
    return 1;
  }
  num_bits_index = btor_util_log_2 (num_elements);
  btor           = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
  indices = (BoolectorNode **) malloc (sizeof (BoolectorNode *) * num_elements);
  isort   = boolector_bitvec_sort (btor, num_bits_index);
  esort   = boolector_bitvec_sort (btor, num_bits);
  asort   = boolector_array_sort (btor, isort, esort);
  for (i = 0; i < num_elements; i++)
    indices[i] = boolector_int (btor, i, isort);
  array = boolector_array (btor, asort, "array");
  /* current maximum is first element of array */
  max = boolector_read (btor, array, indices[0]);
  /* compute maximum of array */
  for (i = 1; i < num_elements; i++)
  {
    read = boolector_read (btor, array, indices[i]);
    ugt  = boolector_ugt (btor, read, max);
    temp = boolector_cond (btor, ugt, read, max);
    boolector_release (btor, max);
    max = temp;
    boolector_release (btor, read);
    boolector_release (btor, ugt);
  }
  /* show that maximum is really the maximum */
  index = boolector_var (btor, isort, "index");
  read  = boolector_read (btor, array, index);
  /* there is no arbitrary read value which is greater than the maximum */
  formula = boolector_ult (btor, max, read);
  boolector_dump_btor_node (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) boolector_release (btor, indices[i]);
  boolector_release (btor, formula);
  boolector_release (btor, read);
  boolector_release (btor, index);
  boolector_release (btor, max);
  boolector_release (btor, array);
  boolector_release_sort (btor, isort);
  boolector_release_sort (btor, esort);
  boolector_release_sort (btor, asort);
  boolector_delete (btor);
  free (indices);
  return 0;
}

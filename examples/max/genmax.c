#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i;
  Btor *btor;
  BtorExp **indices, *array, *ugt, *temp, *read, *formula, *max, *index;
  if (argc != 3)
  {
    printf ("Usage: ./genmax <num-bits> <num-elements>\n");
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
  if (!btor_is_power_of_2_util (num_elements))
  {
    printf ("Number of elements must be a power of two\n");
    return 1;
  }
  num_bits_index = btor_log_2_util (num_elements);
  btor           = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);
  indices = (BtorExp **) malloc (sizeof (BtorExp *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = btor_int_to_exp (btor, i, num_bits_index);
  array = btor_array_exp (btor, num_bits, num_bits_index);
  /* current maximum is first element of array */
  max = btor_read_exp (btor, array, indices[0]);
  /* compute maximum of array */
  for (i = 1; i < num_elements; i++)
  {
    read = btor_read_exp (btor, array, indices[i]);
    ugt  = btor_ugt_exp (btor, read, max);
    temp = btor_cond_exp (btor, ugt, read, max);
    btor_release_exp (btor, max);
    max = temp;
    btor_release_exp (btor, read);
    btor_release_exp (btor, ugt);
  }
  /* show that maximum is really the maximum */
  index = btor_var_exp (btor, num_bits_index, "index");
  read  = btor_read_exp (btor, array, index);
  /* there is no arbitrary read value which is greater than the maximum */
  formula = btor_ult_exp (btor, max, read);
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (btor, indices[i]);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, read);
  btor_release_exp (btor, index);
  btor_release_exp (btor, max);
  btor_release_exp (btor, array);
  btor_delete_btor (btor);
  free (indices);
  return 0;
}

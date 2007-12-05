#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i;
  Btor *btor;
  BtorExp **indices, *array, *eq, *temp, *read, *formula, *val, *index, *found;
  if (argc != 3)
  {
    printf ("Usage: ./genlinearsearch <num-bits> <num-elements>\n");
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
  /* we write arbitrary search value into array at an arbitrary index */
  val   = btor_var_exp (btor, num_bits, "search_val");
  index = btor_var_exp (btor, num_bits_index, "search_index");
  temp  = btor_write_exp (btor, array, index, val);
  btor_release_exp (btor, array);
  array = temp;
  found = btor_const_exp (btor, "0");
  /* we search */
  for (i = 0; i < num_elements; i++)
  {
    read = btor_read_exp (btor, array, indices[i]);
    eq   = btor_eq_exp (btor, read, val);
    temp = btor_or_exp (btor, found, eq);
    btor_release_exp (btor, found);
    found = temp;
    btor_release_exp (btor, read);
    btor_release_exp (btor, eq);
  }
  /* we negate the formula and show that it is unsatisfiable */
  formula = btor_not_exp (btor, found);
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (btor, indices[i]);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, index);
  btor_release_exp (btor, val);
  btor_release_exp (btor, found);
  btor_release_exp (btor, array);
  btor_delete_btor (btor);
  free (indices);
  return 0;
}

#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"
#include "utils/btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i;
  Btor *btor;
  BoolectorNode **indices, *array, *eq;
  BoolectorNode *temp, *read, *formula, *val, *index, *found;
  if (argc != 3)
  {
    printf ("Usage: ./linearsearch <num-bits> <num-elements>\n");
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
  btor           = boolector_new ();
  boolector_set_opt (btor, "rewrite_leve", 0);
  indices = (BoolectorNode **) malloc (sizeof (BoolectorNode *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = boolector_int (btor, i, num_bits_index);
  array = boolector_array (btor, num_bits, num_bits_index, "array");
  /* we write arbitrary search value into array at an arbitrary index */
  val   = boolector_var (btor, num_bits, "search_val");
  index = boolector_var (btor, num_bits_index, "search_index");
  temp  = boolector_write (btor, array, index, val);
  boolector_release (btor, array);
  array = temp;
  found = boolector_const (btor, "0");
  /* we search */
  for (i = 0; i < num_elements; i++)
  {
    read = boolector_read (btor, array, indices[i]);
    eq   = boolector_eq (btor, read, val);
    temp = boolector_or (btor, found, eq);
    boolector_release (btor, found);
    found = temp;
    boolector_release (btor, read);
    boolector_release (btor, eq);
  }
  /* we negate the formula and show that it is unsatisfiable */
  formula = boolector_not (btor, found);
  boolector_dump_btor_node (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) boolector_release (btor, indices[i]);
  boolector_release (btor, formula);
  boolector_release (btor, index);
  boolector_release (btor, val);
  boolector_release (btor, found);
  boolector_release (btor, array);
  boolector_delete (btor);
  free (indices);
  return 0;
}

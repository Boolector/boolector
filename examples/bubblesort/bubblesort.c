#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i, j;
  Btor *btor;
  BtorExp **indices, *array, *ne, *ugt, *ulte, *temp, *read1;
  BtorExp *read2, *cond1, *cond2, *sorted;
  BtorExp *no_diff_element, *formula, *index, *old_element;
  if (argc != 3)
  {
    printf ("Usage: ./bubblesort <num-bits> <num-elements>\n");
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
  /* read at an arbitrary index (needed later): */
  index       = btor_var_exp (btor, num_bits_index, "index");
  old_element = btor_read_exp (btor, array, index);
  /* bubble sort algorithm */
  for (i = 1; i < num_elements; i++)
  {
    for (j = 0; j < num_elements - i; j++)
    {
      read1 = btor_read_exp (btor, array, indices[j]);
      read2 = btor_read_exp (btor, array, indices[j + 1]);
      ugt   = btor_ugt_exp (btor, read1, read2);
      /* swap ? */
      cond1 = btor_cond_exp (btor, ugt, read2, read1);
      cond2 = btor_cond_exp (btor, ugt, read1, read2);
      temp  = btor_write_exp (btor, array, indices[j], cond1);
      btor_release_exp (btor, array);
      array = temp;
      temp  = btor_write_exp (btor, array, indices[j + 1], cond2);
      btor_release_exp (btor, array);
      array = temp;
      btor_release_exp (btor, read1);
      btor_release_exp (btor, read2);
      btor_release_exp (btor, ugt);
      btor_release_exp (btor, cond1);
      btor_release_exp (btor, cond2);
    }
  }
  /* show that array is sorted */
  sorted = btor_const_exp (btor, "1");
  for (i = 0; i < num_elements - 1; i++)
  {
    read1 = btor_read_exp (btor, array, indices[i]);
    read2 = btor_read_exp (btor, array, indices[i + 1]);
    ulte  = btor_ulte_exp (btor, read1, read2);
    temp  = btor_and_exp (btor, sorted, ulte);
    btor_release_exp (btor, sorted);
    sorted = temp;
    btor_release_exp (btor, read1);
    btor_release_exp (btor, read2);
    btor_release_exp (btor, ulte);
  }
  /* It is not the case that there exists an element in
   * the initial array which does not occur in the sorted
   * array.*/
  no_diff_element = btor_const_exp (btor, "1");
  for (i = 0; i < num_elements; i++)
  {
    read1 = btor_read_exp (btor, array, indices[i]);
    ne    = btor_ne_exp (btor, read1, old_element);
    temp  = btor_and_exp (btor, no_diff_element, ne);
    btor_release_exp (btor, no_diff_element);
    no_diff_element = temp;
    btor_release_exp (btor, read1);
    btor_release_exp (btor, ne);
  }
  temp = btor_not_exp (btor, no_diff_element);
  btor_release_exp (btor, no_diff_element);
  no_diff_element = temp;
  /* we conjunct this with the sorted predicate */
  formula = btor_and_exp (btor, sorted, no_diff_element);
  /* we negate the formula and show that it is unsatisfiable */
  temp = btor_not_exp (btor, formula);
  btor_release_exp (btor, formula);
  formula = temp;
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (btor, indices[i]);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, sorted);
  btor_release_exp (btor, no_diff_element);
  btor_release_exp (btor, old_element);
  btor_release_exp (btor, index);
  btor_release_exp (btor, array);
  btor_delete_btor (btor);
  free (indices);
  return 0;
}

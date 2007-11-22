#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i, j;
  Btor *btor;
  BtorExp **indices, *array, *min_index, *min_element, *cur_element,
      *old_element, *index;
  BtorExp *ne, *ult, *ulte, *temp, *read1, *read2, *no_diff_element, *sorted,
      *formula;
  if (argc != 3)
  {
    printf ("Usage: ./genselectionsort <num-bits> <num-elements>\n");
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
  indices        = (BtorExp **) malloc (sizeof (BtorExp *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = btor_int_to_exp (btor, i, num_bits_index);
  array = btor_array_exp (btor, num_bits, num_bits_index);
  /* read at an arbitrary index (needed later): */
  index       = btor_var_exp (btor, num_bits_index, "index");
  old_element = btor_read_exp (btor, array, index);
  /* selection sort algorithm */
  for (i = 0; i < num_elements - 1; i++)
  {
    min_element = btor_read_exp (btor, array, indices[i]);
    min_index   = btor_copy_exp (btor, indices[i]);
    for (j = i + 1; j < num_elements; j++)
    {
      cur_element = btor_read_exp (btor, array, indices[j]);
      ult         = btor_ult_exp (btor, cur_element, min_element);
      /* found new minimum ? */
      temp = btor_cond_exp (btor, ult, cur_element, min_element);
      btor_release_exp (btor, min_element);
      min_element = temp;
      /* new minimium index ? */
      temp = btor_cond_exp (btor, ult, indices[j], min_index);
      btor_release_exp (btor, min_index);
      min_index = temp;
      /* clean up */
      btor_release_exp (btor, cur_element);
      btor_release_exp (btor, ult);
    }
    /* swap elements */
    read1 = btor_read_exp (btor, array, min_index);
    read2 = btor_read_exp (btor, array, indices[i]);
    temp  = btor_write_exp (btor, array, indices[i], read1);
    btor_release_exp (btor, array);
    array = temp;
    temp  = btor_write_exp (btor, array, min_index, read2);
    btor_release_exp (btor, array);
    array = temp;
    /* clean up */
    btor_release_exp (btor, read1);
    btor_release_exp (btor, read2);
    btor_release_exp (btor, min_index);
    btor_release_exp (btor, min_element);
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
  /* we show that every element of the initial array
   * occurs in the final sorted array by showing that
   * there is no counter example:
   * It is not the case that there exists an element in
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
  btor_release_exp (btor, old_element);
  btor_release_exp (btor, index);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, no_diff_element);
  btor_release_exp (btor, sorted);
  btor_release_exp (btor, array);
  btor_delete_btor (btor);
  free (indices);
  return 0;
}

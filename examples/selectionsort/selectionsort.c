#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"
#include "btoropt.h"
#include "utils/btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i, j;
  Btor *btor;
  BoolectorNode **indices, *array, *min_index, *min_element, *cur_element;
  BoolectorNode *old_element, *index, *ne, *ult, *ulte, *temp, *read1, *read2;
  BoolectorNode *no_diff_element, *sorted, *formula;
  BoolectorSort isort, esort, asort;
  if (argc != 3)
  {
    printf ("Usage: ./selectionsort <num-bits> <num-elements>\n");
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
  /* read at an arbitrary index (needed later): */
  index       = boolector_var (btor, isort, "index");
  old_element = boolector_read (btor, array, index);
  /* selection sort algorithm */
  for (i = 0; i < num_elements - 1; i++)
  {
    min_element = boolector_read (btor, array, indices[i]);
    min_index   = boolector_copy (btor, indices[i]);
    for (j = i + 1; j < num_elements; j++)
    {
      cur_element = boolector_read (btor, array, indices[j]);
      ult         = boolector_ult (btor, cur_element, min_element);
      /* found new minimum ? */
      temp = boolector_cond (btor, ult, cur_element, min_element);
      boolector_release (btor, min_element);
      min_element = temp;
      /* new minimium index ? */
      temp = boolector_cond (btor, ult, indices[j], min_index);
      boolector_release (btor, min_index);
      min_index = temp;
      /* clean up */
      boolector_release (btor, cur_element);
      boolector_release (btor, ult);
    }
    /* swap elements */
    read1 = boolector_read (btor, array, min_index);
    read2 = boolector_read (btor, array, indices[i]);
    temp  = boolector_write (btor, array, indices[i], read1);
    boolector_release (btor, array);
    array = temp;
    temp  = boolector_write (btor, array, min_index, read2);
    boolector_release (btor, array);
    array = temp;
    /* clean up */
    boolector_release (btor, read1);
    boolector_release (btor, read2);
    boolector_release (btor, min_index);
    boolector_release (btor, min_element);
  }
  /* show that array is sorted */
  sorted = boolector_const (btor, "1");
  for (i = 0; i < num_elements - 1; i++)
  {
    read1 = boolector_read (btor, array, indices[i]);
    read2 = boolector_read (btor, array, indices[i + 1]);
    ulte  = boolector_ulte (btor, read1, read2);
    temp  = boolector_and (btor, sorted, ulte);
    boolector_release (btor, sorted);
    sorted = temp;
    boolector_release (btor, read1);
    boolector_release (btor, read2);
    boolector_release (btor, ulte);
  }
  /* It is not the case that there exists an element in
   * the initial array which does not occur in the sorted
   * array.*/
  no_diff_element = boolector_const (btor, "1");
  for (i = 0; i < num_elements; i++)
  {
    read1 = boolector_read (btor, array, indices[i]);
    ne    = boolector_ne (btor, read1, old_element);
    temp  = boolector_and (btor, no_diff_element, ne);
    boolector_release (btor, no_diff_element);
    no_diff_element = temp;
    boolector_release (btor, read1);
    boolector_release (btor, ne);
  }
  temp = boolector_not (btor, no_diff_element);
  boolector_release (btor, no_diff_element);
  no_diff_element = temp;
  /* we conjunct this with the sorted predicate */
  formula = boolector_and (btor, sorted, no_diff_element);
  /* we negate the formula and show that it is unsatisfiable */
  temp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = temp;
  boolector_dump_btor_node (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) boolector_release (btor, indices[i]);
  boolector_release (btor, old_element);
  boolector_release (btor, index);
  boolector_release (btor, formula);
  boolector_release (btor, no_diff_element);
  boolector_release (btor, sorted);
  boolector_release (btor, array);
  boolector_release_sort (btor, isort);
  boolector_release_sort (btor, esort);
  boolector_release_sort (btor, asort);
  boolector_delete (btor);
  free (indices);
  return 0;
}

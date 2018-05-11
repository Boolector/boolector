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
  BoolectorNode **indices, *array, *ne, *ugt, *ulte, *temp, *read1;
  BoolectorNode *read2, *cond1, *cond2, *sorted;
  BoolectorNode *no_diff_element, *formula, *index, *old_element;
  BoolectorSort sort_index, sort_elem, sort_array;
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
  if (!btor_util_is_power_of_2 (num_elements))
  {
    printf ("Number of elements must be a power of two\n");
    return 1;
  }
  num_bits_index = btor_util_log_2 (num_elements);
  btor           = boolector_new ();
  sort_index     = boolector_bitvec_sort (btor, num_bits_index);
  sort_elem      = boolector_bitvec_sort (btor, num_bits);
  sort_array     = boolector_array_sort (btor, sort_index, sort_elem);
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
  indices = (BoolectorNode **) malloc (sizeof (BoolectorNode *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = boolector_int (btor, i, sort_index);
  array = boolector_array (btor, sort_array, "array");
  /* read at an arbitrary index (needed later): */
  index       = boolector_var (btor, sort_index, "index");
  old_element = boolector_read (btor, array, index);
  /* bubble sort algorithm */
  for (i = 1; i < num_elements; i++)
  {
    for (j = 0; j < num_elements - i; j++)
    {
      read1 = boolector_read (btor, array, indices[j]);
      read2 = boolector_read (btor, array, indices[j + 1]);
      ugt   = boolector_ugt (btor, read1, read2);
      /* swap ? */
      cond1 = boolector_cond (btor, ugt, read2, read1);
      cond2 = boolector_cond (btor, ugt, read1, read2);
      temp  = boolector_write (btor, array, indices[j], cond1);
      boolector_release (btor, array);
      array = temp;
      temp  = boolector_write (btor, array, indices[j + 1], cond2);
      boolector_release (btor, array);
      array = temp;
      boolector_release (btor, read1);
      boolector_release (btor, read2);
      boolector_release (btor, ugt);
      boolector_release (btor, cond1);
      boolector_release (btor, cond2);
    }
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
  boolector_release (btor, formula);
  boolector_release (btor, sorted);
  boolector_release (btor, no_diff_element);
  boolector_release (btor, old_element);
  boolector_release (btor, index);
  boolector_release (btor, array);
  boolector_release_sort (btor, sort_index);
  boolector_release_sort (btor, sort_elem);
  boolector_release_sort (btor, sort_array);
  boolector_delete (btor);
  free (indices);
  return 0;
}

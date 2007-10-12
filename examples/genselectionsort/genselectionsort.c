#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits             = 0;
  int num_bits_index       = 0;
  int num_elements         = 0;
  int i                    = 0;
  int j                    = 0;
  BtorExpMgr *emgr         = NULL;
  BtorExp **indices        = NULL;
  BtorExp *array           = NULL;
  BtorExp *min_index       = NULL;
  BtorExp *min_element     = NULL;
  BtorExp *cur_element     = NULL;
  BtorExp *old_element     = NULL;
  BtorExp *index           = NULL;
  BtorExp *ne              = NULL;
  BtorExp *slt             = NULL;
  BtorExp *slte            = NULL;
  BtorExp *temp            = NULL;
  BtorExp *read1           = NULL;
  BtorExp *read2           = NULL;
  BtorExp *no_diff_element = NULL;
  BtorExp *sorted          = NULL;
  BtorExp *formula         = NULL;
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
  emgr           = btor_new_exp_mgr (2, 0, 0, stdout);
  indices        = (BtorExp **) malloc (sizeof (BtorExp *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = btor_int_to_exp (emgr, i, num_bits_index);
  array = btor_array_exp (emgr, num_bits, num_bits_index);
  index = btor_var_exp (emgr, num_bits_index, "oldvalue");
  /* read at an arbitrary index (needed later): */
  old_element = btor_read_exp (emgr, array, index);
  /* selection sort algorithm */
  for (i = 0; i < num_elements - 1; i++)
  {
    min_element = btor_read_exp (emgr, array, indices[i]);
    min_index   = btor_copy_exp (emgr, indices[i]);
    for (j = i + 1; j < num_elements; j++)
    {
      cur_element = btor_read_exp (emgr, array, indices[j]);
      slt         = btor_slt_exp (emgr, cur_element, min_element);
      /* found new minimum ? */
      temp = btor_cond_exp (emgr, slt, cur_element, min_element);
      btor_release_exp (emgr, min_element);
      min_element = temp;
      /* new minimium index ? */
      temp = btor_cond_exp (emgr, slt, indices[j], min_index);
      btor_release_exp (emgr, min_index);
      min_index = temp;
      /* clean up */
      btor_release_exp (emgr, cur_element);
      btor_release_exp (emgr, slt);
    }
    /* swap elements */
    read1 = btor_read_exp (emgr, array, min_index);
    read2 = btor_read_exp (emgr, array, indices[i]);
    temp  = btor_write_exp (emgr, array, indices[i], read1);
    btor_release_exp (emgr, array);
    array = temp;
    temp  = btor_write_exp (emgr, array, min_index, read2);
    btor_release_exp (emgr, array);
    array = temp;
    /* clean up */
    btor_release_exp (emgr, read1);
    btor_release_exp (emgr, read2);
    btor_release_exp (emgr, min_index);
    btor_release_exp (emgr, min_element);
  }
  /* show that array is sorted */
  sorted = btor_const_exp (emgr, "1");
  for (i = 0; i < num_elements - 1; i++)
  {
    read1 = btor_read_exp (emgr, array, indices[i]);
    read2 = btor_read_exp (emgr, array, indices[i + 1]);
    slte  = btor_slte_exp (emgr, read1, read2);
    temp  = btor_and_exp (emgr, sorted, slte);
    btor_release_exp (emgr, sorted);
    sorted = temp;
    btor_release_exp (emgr, read1);
    btor_release_exp (emgr, read2);
    btor_release_exp (emgr, slte);
  }
  /* we show that every element of the initial array
   * occurs in the final sorted array by showing that
   * there is no counter example:
   * It is not the case that there exists an element in
   * the initial array which does not occur in the sorted
   * array.*/
  no_diff_element = btor_const_exp (emgr, "1");
  for (i = 0; i < num_elements; i++)
  {
    read1 = btor_read_exp (emgr, array, indices[i]);
    ne    = btor_ne_exp (emgr, read1, old_element);
    temp  = btor_and_exp (emgr, no_diff_element, ne);
    btor_release_exp (emgr, no_diff_element);
    no_diff_element = temp;
    btor_release_exp (emgr, read1);
    btor_release_exp (emgr, ne);
  }
  temp = btor_not_exp (emgr, no_diff_element);
  btor_release_exp (emgr, no_diff_element);
  no_diff_element = temp;
  /* we conjunct this with the sorted predicate */
  formula = btor_and_exp (emgr, sorted, no_diff_element);
  /* we negate the formula and show that it is unsatisfiable */
  temp = btor_not_exp (emgr, formula);
  btor_release_exp (emgr, formula);
  formula = temp;
  btor_dump_exp (emgr, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (emgr, indices[i]);
  btor_release_exp (emgr, old_element);
  btor_release_exp (emgr, index);
  btor_release_exp (emgr, formula);
  btor_release_exp (emgr, no_diff_element);
  btor_release_exp (emgr, sorted);
  btor_release_exp (emgr, array);
  btor_delete_exp_mgr (emgr);
  free (indices);
  return 0;
}

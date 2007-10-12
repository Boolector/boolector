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
  BtorExp *ne              = NULL;
  BtorExp *ugt             = NULL;
  BtorExp *ulte            = NULL;
  BtorExp *temp            = NULL;
  BtorExp *read1           = NULL;
  BtorExp *read2           = NULL;
  BtorExp *cond1           = NULL;
  BtorExp *cond2           = NULL;
  BtorExp *sorted          = NULL;
  BtorExp *no_diff_element = NULL;
  BtorExp *formula         = NULL;
  BtorExp *index           = NULL;
  BtorExp *old_element     = NULL;
  if (argc != 3)
  {
    printf ("Usage: ./genbubblesort <num-bits> <num-elements>\n");
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
  /* bubble sort algorithm */
  for (i = 1; i < num_elements; i++)
  {
    for (j = 0; j < num_elements - i; j++)
    {
      read1 = btor_read_exp (emgr, array, indices[j]);
      read2 = btor_read_exp (emgr, array, indices[j + 1]);
      ugt   = btor_ugt_exp (emgr, read1, read2);
      /* swap ? */
      cond1 = btor_cond_exp (emgr, ugt, read2, read1);
      cond2 = btor_cond_exp (emgr, ugt, read1, read2);
      temp  = btor_write_exp (emgr, array, indices[j], cond1);
      btor_release_exp (emgr, array);
      array = temp;
      temp  = btor_write_exp (emgr, array, indices[j + 1], cond2);
      btor_release_exp (emgr, array);
      array = temp;
      btor_release_exp (emgr, read1);
      btor_release_exp (emgr, read2);
      btor_release_exp (emgr, ugt);
      btor_release_exp (emgr, cond1);
      btor_release_exp (emgr, cond2);
    }
  }
  /* show that array is sorted */
  sorted = btor_const_exp (emgr, "1");
  for (i = 0; i < num_elements - 1; i++)
  {
    read1 = btor_read_exp (emgr, array, indices[i]);
    read2 = btor_read_exp (emgr, array, indices[i + 1]);
    ulte  = btor_ulte_exp (emgr, read1, read2);
    temp  = btor_and_exp (emgr, sorted, ulte);
    btor_release_exp (emgr, sorted);
    sorted = temp;
    btor_release_exp (emgr, read1);
    btor_release_exp (emgr, read2);
    btor_release_exp (emgr, ulte);
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
  btor_release_exp (emgr, formula);
  btor_release_exp (emgr, sorted);
  btor_release_exp (emgr, no_diff_element);
  btor_release_exp (emgr, old_element);
  btor_release_exp (emgr, index);
  btor_release_exp (emgr, array);
  btor_delete_exp_mgr (emgr);
  free (indices);
  return 0;
}

#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i, j;
  Btor *btor;
  BtorExp **indices, *array_bubble, *array_selection, *ult, *ugt;
  BtorExp *read1, *read2, *cond1, *cond2, *formula, *min_element;
  BtorExp *cur_element, *min_index, *temp;
  if (argc != 3)
  {
    printf ("Usage: ./genselectionbubblesort <num-bits> <num-elements>\n");
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
  array_bubble    = btor_array_exp (btor, num_bits, num_bits_index);
  array_selection = btor_copy_exp (btor, array_bubble);
  /* bubble sort algorithm */
  for (i = 1; i < num_elements; i++)
  {
    for (j = 0; j < num_elements - i; j++)
    {
      read1 = btor_read_exp (btor, array_bubble, indices[j]);
      read2 = btor_read_exp (btor, array_bubble, indices[j + 1]);
      ugt   = btor_ugt_exp (btor, read1, read2);
      /* swap ? */
      cond1 = btor_cond_exp (btor, ugt, read2, read1);
      cond2 = btor_cond_exp (btor, ugt, read1, read2);
      temp  = btor_write_exp (btor, array_bubble, indices[j], cond1);
      btor_release_exp (btor, array_bubble);
      array_bubble = temp;
      temp         = btor_write_exp (btor, array_bubble, indices[j + 1], cond2);
      btor_release_exp (btor, array_bubble);
      array_bubble = temp;
      btor_release_exp (btor, read1);
      btor_release_exp (btor, read2);
      btor_release_exp (btor, ugt);
      btor_release_exp (btor, cond1);
      btor_release_exp (btor, cond2);
    }
  }
  /* selection sort algorithm */
  for (i = 0; i < num_elements - 1; i++)
  {
    min_element = btor_read_exp (btor, array_selection, indices[i]);
    min_index   = btor_copy_exp (btor, indices[i]);
    for (j = i + 1; j < num_elements; j++)
    {
      cur_element = btor_read_exp (btor, array_selection, indices[j]);
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
    read1 = btor_read_exp (btor, array_selection, min_index);
    read2 = btor_read_exp (btor, array_selection, indices[i]);
    temp  = btor_write_exp (btor, array_selection, indices[i], read1);
    btor_release_exp (btor, array_selection);
    array_selection = temp;
    temp            = btor_write_exp (btor, array_selection, min_index, read2);
    btor_release_exp (btor, array_selection);
    array_selection = temp;
    /* clean up */
    btor_release_exp (btor, read1);
    btor_release_exp (btor, read2);
    btor_release_exp (btor, min_index);
    btor_release_exp (btor, min_element);
  }
  /* 'array_bubble' and 'array_selection' must be equal */
  formula = btor_eq_exp (btor, array_bubble, array_selection);
  /* we negate the formula and show that it is unsatisfiable */
  temp = btor_not_exp (btor, formula);
  btor_release_exp (btor, formula);
  formula = temp;
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (btor, indices[i]);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, array_bubble);
  btor_release_exp (btor, array_selection);
  btor_delete_btor (btor);
  free (indices);
  return 0;
}

#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_elements, i, j;
  Btor *btor;
  BtorExp *mem, *ne, *ugte, *ulte, *ult, *temp, *read1;
  BtorExp *read2, *sorted, *pos, *pos_p_1, *min_index;
  BtorExp *no_diff_element, *formula, *index, *old_element;
  BtorExp *num_elements_exp, *start, *top, *one, *range_index;
  BtorExp *implies, *i_pos, *j_pos, *cur_element, *min_element;
  if (argc != 2)
  {
    printf ("Usage: ./selectionsortmem <num-elements>\n");
    return 1;
  }
  num_elements = atoi (argv[1]);
  if (num_elements <= 1)
  {
    printf ("Number of elements must be greater than one\n");
    return 1;
  }

  btor = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);
  one = btor_one_exp (btor, 32);

  mem = btor_array_exp (btor, 8, 32);
  /* first index */
  start            = btor_var_exp (btor, 32, "start");
  num_elements_exp = btor_unsigned_to_exp (btor, num_elements, 32);
  /* last index + 1 */
  top = btor_add_exp (btor, start, num_elements_exp);

  /* read at an arbitrary index inside the sequence (needed later): */
  index       = btor_var_exp (btor, 32, "index");
  ugte        = btor_ugte_exp (btor, index, start);
  ult         = btor_ult_exp (btor, index, top);
  range_index = btor_and_exp (btor, ugte, ult);
  btor_release_exp (btor, ugte);
  btor_release_exp (btor, ult);
  old_element = btor_read_exp (btor, mem, index);

  /* selection sort algorithm */
  i_pos = btor_copy_exp (btor, start);
  for (i = 0; i < num_elements - 1; i++)
  {
    min_element = btor_read_exp (btor, mem, i_pos);
    min_index   = btor_copy_exp (btor, i_pos);
    j_pos       = btor_add_exp (btor, i_pos, one);
    for (j = i + 1; j < num_elements; j++)
    {
      cur_element = btor_read_exp (btor, mem, j_pos);
      ult         = btor_ult_exp (btor, cur_element, min_element);
      /* found new minimum ? */
      temp = btor_cond_exp (btor, ult, cur_element, min_element);
      btor_release_exp (btor, min_element);
      min_element = temp;
      /* new minimium index ? */
      temp = btor_cond_exp (btor, ult, j_pos, min_index);
      btor_release_exp (btor, min_index);
      min_index = temp;

      /* clean up */
      btor_release_exp (btor, cur_element);
      btor_release_exp (btor, ult);

      /* j++ */
      temp = btor_add_exp (btor, j_pos, one);
      btor_release_exp (btor, j_pos);
      j_pos = temp;
    }
    btor_release_exp (btor, j_pos);

    /* swap elements */
    read1 = btor_read_exp (btor, mem, min_index);
    read2 = btor_read_exp (btor, mem, i_pos);
    temp  = btor_write_exp (btor, mem, i_pos, read1);
    btor_release_exp (btor, mem);
    mem  = temp;
    temp = btor_write_exp (btor, mem, min_index, read2);
    btor_release_exp (btor, mem);
    mem = temp;

    /* clean up */
    btor_release_exp (btor, read1);
    btor_release_exp (btor, read2);
    btor_release_exp (btor, min_index);
    btor_release_exp (btor, min_element);

    /* i++ */
    temp = btor_add_exp (btor, i_pos, one);
    btor_release_exp (btor, i_pos);
    i_pos = temp;
  }
  btor_release_exp (btor, i_pos);

  /* show that sequence is sorted */
  sorted  = btor_true_exp (btor);
  pos     = btor_copy_exp (btor, start);
  pos_p_1 = btor_add_exp (btor, pos, one);
  for (i = 0; i < num_elements - 1; i++)
  {
    read1 = btor_read_exp (btor, mem, pos);
    read2 = btor_read_exp (btor, mem, pos_p_1);
    ulte  = btor_ulte_exp (btor, read1, read2);
    temp  = btor_and_exp (btor, sorted, ulte);
    btor_release_exp (btor, sorted);
    sorted = temp;
    btor_release_exp (btor, read1);
    btor_release_exp (btor, read2);
    btor_release_exp (btor, ulte);

    btor_release_exp (btor, pos);
    pos = btor_copy_exp (btor, pos_p_1);
    btor_release_exp (btor, pos_p_1);
    pos_p_1 = btor_add_exp (btor, pos, one);
  }
  btor_release_exp (btor, pos);
  btor_release_exp (btor, pos_p_1);

  formula = sorted;

  /* It is not the case that there exists an element in
   * the initial sequence which does not occur in the sorted
   * sequence.*/
  no_diff_element = btor_true_exp (btor);
  pos             = btor_copy_exp (btor, start);
  for (i = 0; i < num_elements; i++)
  {
    read1 = btor_read_exp (btor, mem, pos);
    ne    = btor_ne_exp (btor, read1, old_element);
    temp  = btor_and_exp (btor, no_diff_element, ne);
    btor_release_exp (btor, no_diff_element);
    no_diff_element = temp;
    btor_release_exp (btor, read1);
    btor_release_exp (btor, ne);
    temp = btor_add_exp (btor, pos, one);
    btor_release_exp (btor, pos);
    pos = temp;
  }
  btor_release_exp (btor, pos);

  temp = btor_not_exp (btor, no_diff_element);
  btor_release_exp (btor, no_diff_element);
  no_diff_element = temp;

  implies = btor_implies_exp (btor, range_index, no_diff_element);

  temp = btor_and_exp (btor, formula, implies);
  btor_release_exp (btor, formula);
  formula = temp;

  btor_release_exp (btor, implies);
  btor_release_exp (btor, no_diff_element);
  btor_release_exp (btor, range_index);

  /* we negate the formula and show that it is unsatisfiable */
  temp = btor_not_exp (btor, formula);
  btor_release_exp (btor, formula);
  formula = temp;
  btor_dump_exp (btor, stdout, formula);

  /* clean up */
  btor_release_exp (btor, formula);
  btor_release_exp (btor, old_element);
  btor_release_exp (btor, index);
  btor_release_exp (btor, mem);
  btor_release_exp (btor, start);
  btor_release_exp (btor, top);
  btor_release_exp (btor, num_elements_exp);
  btor_release_exp (btor, one);
  btor_delete_btor (btor);
  return 0;
}

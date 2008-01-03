#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../boolector.h"
#include "../../btorutil.h"

static int
num_chars (int x)
{
  int result = 0;
  if (x == 0) return 1;
  while (x > 0)
  {
    result++;
    x /= 10;
  }
  return result;
}

int
main (int argc, char **argv)
{
  int num_elements, i, j;
  char *buffer;
  Btor *btor;
  BtorExp **initial_elements, **sorted_elements, *mem;
  BtorExp *ugt, *ulte, *temp, *read1, *start, *top, *pos, *pos_p_1,
      *num_elements_exp;
  BtorExp *read2, *cond1, *cond2, *sorted, *formula, *eq, *var, *one;
  if (argc != 2)
  {
    printf ("Usage: ./bubblesortmemexample <num-elements>\n");
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

  initial_elements = (BtorExp **) malloc (sizeof (BtorExp *) * num_elements);
  sorted_elements  = (BtorExp **) malloc (sizeof (BtorExp *) * num_elements);

  one              = btor_one_exp (btor, 32);
  start            = btor_var_exp (btor, 32, "start");
  num_elements_exp = btor_unsigned_to_exp (btor, num_elements, 32);
  /* last index + 1 */
  top = btor_add_exp (btor, start, num_elements_exp);

  mem = btor_array_exp (btor, 8, 32);

  /* read initial elements */
  pos = btor_copy_exp (btor, start);
  for (i = 0; i < num_elements; i++)
  {
    initial_elements[i] = btor_read_exp (btor, mem, pos);
    temp                = btor_add_exp (btor, pos, one);
    btor_release_exp (btor, pos);
    pos = temp;
  }
  btor_release_exp (btor, pos);

  /* bubble sort algorithm */
  for (i = 1; i < num_elements; i++)
  {
    pos     = btor_copy_exp (btor, start);
    pos_p_1 = btor_add_exp (btor, pos, one);
    for (j = 0; j < num_elements - i; j++)
    {
      read1 = btor_read_exp (btor, mem, pos);
      read2 = btor_read_exp (btor, mem, pos_p_1);
      ugt   = btor_ugt_exp (btor, read1, read2);
      /* swap ? */
      cond1 = btor_cond_exp (btor, ugt, read2, read1);
      cond2 = btor_cond_exp (btor, ugt, read1, read2);
      temp  = btor_write_exp (btor, mem, pos, cond1);
      btor_release_exp (btor, mem);
      mem  = temp;
      temp = btor_write_exp (btor, mem, pos_p_1, cond2);
      btor_release_exp (btor, mem);
      mem = temp;

      btor_release_exp (btor, read1);
      btor_release_exp (btor, read2);
      btor_release_exp (btor, ugt);
      btor_release_exp (btor, cond1);
      btor_release_exp (btor, cond2);

      btor_release_exp (btor, pos);
      pos = btor_copy_exp (btor, pos_p_1);
      btor_release_exp (btor, pos_p_1);
      pos_p_1 = btor_add_exp (btor, pos, one);
    }
    btor_release_exp (btor, pos);
    btor_release_exp (btor, pos_p_1);
  }

  /* read sorted elements */
  pos = btor_copy_exp (btor, start);
  for (i = 0; i < num_elements; i++)
  {
    sorted_elements[i] = btor_read_exp (btor, mem, pos);
    temp               = btor_add_exp (btor, pos, one);
    btor_release_exp (btor, pos);
    pos = temp;
  }
  btor_release_exp (btor, pos);

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

  formula = btor_copy_exp (btor, sorted);

  /* we set variables equal to the initial read values */
  for (i = 0; i < num_elements; i++)
  {
    buffer = (char *) malloc (sizeof (char)
                              * (strlen ("initial_v") + num_chars (i) + 1));
    sprintf (buffer, "inital_v%d", i);
    var  = btor_var_exp (btor, 8, buffer);
    eq   = btor_eq_exp (btor, var, initial_elements[i]);
    temp = btor_and_exp (btor, formula, eq);
    btor_release_exp (btor, formula);
    formula = temp;
    btor_release_exp (btor, var);
    btor_release_exp (btor, eq);
    free (buffer);
  }

  /* we set variables equal to the sorted read read values */
  for (i = 0; i < num_elements; i++)
  {
    buffer = (char *) malloc (sizeof (char)
                              * (strlen ("sorted_v") + num_chars (i) + 1));
    sprintf (buffer, "sorted_v%d", i);
    var  = btor_var_exp (btor, 8, buffer);
    eq   = btor_eq_exp (btor, var, sorted_elements[i]);
    temp = btor_and_exp (btor, formula, eq);
    btor_release_exp (btor, formula);
    formula = temp;
    btor_release_exp (btor, var);
    btor_release_exp (btor, eq);
    free (buffer);
  }
  btor_dump_exp (btor, stdout, formula);

  /* clean up */
  for (i = 0; i < num_elements; i++)
  {
    btor_release_exp (btor, initial_elements[i]);
    btor_release_exp (btor, sorted_elements[i]);
  }
  btor_release_exp (btor, formula);
  btor_release_exp (btor, sorted);
  btor_release_exp (btor, mem);
  btor_release_exp (btor, start);
  btor_release_exp (btor, top);
  btor_release_exp (btor, one);
  btor_release_exp (btor, num_elements_exp);
  btor_delete_btor (btor);
  free (initial_elements);
  free (sorted_elements);
  return 0;
}

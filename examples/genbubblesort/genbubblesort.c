#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

static void
int_to_bin (int x, char *buffer, int len)
{
  int i = 0;
  for (i = len - 1; i >= 0; i--)
  {
    if (x % 2)
      buffer[i] = '1';
    else
      buffer[i] = '0';
    x >>= 1;
  }
  buffer[len] = '\0';
}

int
main (int argc, char **argv)
{
  int num_bits       = 0;
  int num_bits_index = 0;
  int num_elements   = 0;
  int i              = 0;
  int j              = 0;
  BtorExpMgr *emgr   = NULL;
  BtorExp **indices  = NULL;
  BtorExp *array     = NULL;
  BtorExp *sgt       = NULL;
  BtorExp *slte      = NULL;
  BtorExp *temp      = NULL;
  BtorExp *read1     = NULL;
  BtorExp *read2     = NULL;
  BtorExp *cond1     = NULL;
  BtorExp *cond2     = NULL;
  BtorExp *sorted    = NULL;
  char *buffer       = NULL;
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
  buffer         = (char *) malloc (sizeof (char) * (num_bits_index + 1));
  for (i = 0; i < num_elements; i++)
  {
    int_to_bin (i, buffer, num_bits_index);
    indices[i] = btor_const_exp (emgr, buffer);
  }
  array = btor_array_exp (emgr, num_bits, num_bits_index);
  for (i = 1; i < num_elements; i++)
  {
    for (j = 0; j < num_elements - i; j++)
    {
      read1 = btor_read_exp (emgr, array, indices[j]);
      read2 = btor_read_exp (emgr, array, indices[j + 1]);
      sgt   = btor_sgt_exp (emgr, read1, read2);
      /* swap ? */
      cond1 = btor_cond_exp (emgr, sgt, read2, read1);
      cond2 = btor_cond_exp (emgr, sgt, read1, read2);
      temp  = btor_write_exp (emgr, array, indices[j], cond1);
      btor_release_exp (emgr, array);
      array = temp;
      temp  = btor_write_exp (emgr, array, indices[j + 1], cond2);
      btor_release_exp (emgr, array);
      array = temp;
      btor_release_exp (emgr, read1);
      btor_release_exp (emgr, read2);
      btor_release_exp (emgr, sgt);
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
    slte  = btor_slte_exp (emgr, read1, read2);
    temp  = btor_and_exp (emgr, sorted, slte);
    btor_release_exp (emgr, sorted);
    sorted = temp;
    btor_release_exp (emgr, read1);
    btor_release_exp (emgr, read2);
    btor_release_exp (emgr, slte);
  }
  /* we negate the formula and show that it is unsatisfiable */
  temp = btor_not_exp (emgr, sorted);
  btor_release_exp (emgr, sorted);
  sorted = temp;
  btor_dump_exp (emgr, stdout, sorted);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (emgr, indices[i]);
  btor_release_exp (emgr, sorted);
  btor_release_exp (emgr, array);
  btor_delete_exp_mgr (emgr);
  free (buffer);
  free (indices);
  return 0;
}

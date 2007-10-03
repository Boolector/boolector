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
  BtorExpMgr *emgr   = NULL;
  BtorExp **indices  = NULL;
  BtorExp *array     = NULL;
  BtorExp *sgt       = NULL;
  BtorExp *temp      = NULL;
  BtorExp *read      = NULL;
  BtorExp *formula   = NULL;
  BtorExp *max       = NULL;
  BtorExp *index     = NULL;
  char *buffer       = NULL;
  if (argc != 3)
  {
    printf ("Usage: ./genmax <num-bits> <num-elements>\n");
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
  /* current maximum is first element of array */
  max = btor_read_exp (emgr, array, indices[0]);
  /* compute maximum of array */
  for (i = 1; i < num_elements; i++)
  {
    read = btor_read_exp (emgr, array, indices[i]);
    sgt  = btor_sgt_exp (emgr, read, max);
    temp = btor_cond_exp (emgr, sgt, read, max);
    btor_release_exp (emgr, max);
    max = temp;
    btor_release_exp (emgr, read);
    btor_release_exp (emgr, sgt);
  }
  /* show that maximum is really the maximum */
  index = btor_var_exp (emgr, num_bits_index, "index");
  read  = btor_read_exp (emgr, array, index);
  /* there is no arbitrary read value which is greater than the maximum */
  formula = btor_slt_exp (emgr, max, read);
  btor_dump_exp (emgr, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (emgr, indices[i]);
  btor_release_exp (emgr, formula);
  btor_release_exp (emgr, read);
  btor_release_exp (emgr, index);
  btor_release_exp (emgr, max);
  btor_release_exp (emgr, array);
  btor_delete_exp_mgr (emgr);
  free (buffer);
  free (indices);
  return 0;
}

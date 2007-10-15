#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits       = 0;
  int num_bits_index = 0;
  int num_elements   = 0;
  int i              = 0;
  int num_iterations = 0;
  BtorExpMgr *emgr   = NULL;
  BtorExp **indices  = NULL;
  BtorExp *array     = NULL;
  BtorExp *eq        = NULL;
  BtorExp *ult       = NULL;
  BtorExp *ulte      = NULL;
  BtorExp *ugt       = NULL;
  BtorExp *temp      = NULL;
  BtorExp *read1     = NULL;
  BtorExp *read2     = NULL;
  BtorExp *formula   = NULL;
  BtorExp *val       = NULL;
  BtorExp *index     = NULL;
  BtorExp *found     = NULL;
  BtorExp *sorted    = NULL;
  BtorExp *low       = NULL;
  BtorExp *high      = NULL;
  BtorExp *two       = NULL;
  BtorExp *one       = NULL;
  BtorExp *mid       = NULL;
  BtorExp *sub       = NULL;
  BtorExp *udiv      = NULL;
  BtorExp *inc       = NULL;
  BtorExp *dec       = NULL;
  if (argc != 3)
  {
    printf ("Usage: ./genbinarysearch <num-bits> <num-elements>\n");
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
    printf ("Number of elements must be at least four\n");
    return 1;
  }
  if (!btor_is_power_of_2_util (num_elements))
  {
    printf ("Number of elements must be a power of two\n");
    return 1;
  }
  num_bits_index = btor_log_2_util (num_elements);
  /* binary search needs log2(size(array)) + 1 iterations in the worst case */
  num_iterations = num_bits_index + 1;
  emgr           = btor_new_exp_mgr (2, 0, 0, stdout);
  indices        = (BtorExp **) malloc (sizeof (BtorExp *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = btor_int_to_exp (emgr, i, num_bits_index);
  array = btor_array_exp (emgr, num_bits, num_bits_index);
  /* we write arbitrary search value into array at an arbitrary index */
  val   = btor_var_exp (emgr, num_bits, "search_val");
  index = btor_var_exp (emgr, num_bits_index, "search_index");
  temp  = btor_write_exp (emgr, array, index, val);
  btor_release_exp (emgr, array);
  array = temp;
  /* we assume that array is sorted */
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
  /* binary search algorithm */
  low   = btor_int_to_exp (emgr, 0, num_bits_index);
  high  = btor_int_to_exp (emgr, num_elements - 1, num_bits_index);
  two   = btor_int_to_exp (emgr, 2, num_bits_index);
  one   = btor_int_to_exp (emgr, 1, num_bits_index);
  found = btor_const_exp (emgr, "0");
  for (i = 0; i < num_iterations; i++)
  {
    /* compute mid */
    sub  = btor_sub_exp (emgr, high, low);
    udiv = btor_udiv_exp (emgr, sub, two);
    mid  = btor_add_exp (emgr, low, udiv);
    /* read mid element */
    read1 = btor_read_exp (emgr, array, mid);
    /* compare element with search val */
    eq  = btor_eq_exp (emgr, val, read1);
    ult = btor_ult_exp (emgr, val, read1);
    ugt = btor_ugt_exp (emgr, val, read1);
    /* found element ? */
    temp = btor_or_exp (emgr, found, eq);
    btor_release_exp (emgr, found);
    found = temp;
    /* adapt high (if necessary) */
    dec  = btor_sub_exp (emgr, mid, one);
    temp = btor_cond_exp (emgr, ult, dec, high);
    btor_release_exp (emgr, high);
    high = temp;
    /* adapt low (if necessary) */
    inc  = btor_add_exp (emgr, mid, one);
    temp = btor_cond_exp (emgr, ugt, inc, low);
    btor_release_exp (emgr, low);
    low = temp;
    btor_release_exp (emgr, sub);
    btor_release_exp (emgr, udiv);
    btor_release_exp (emgr, mid);
    btor_release_exp (emgr, eq);
    btor_release_exp (emgr, ult);
    btor_release_exp (emgr, ugt);
    btor_release_exp (emgr, read1);
    btor_release_exp (emgr, inc);
    btor_release_exp (emgr, dec);
  }
  /* the array is sorted implies that we have found the element */
  formula = btor_implies_exp (emgr, sorted, found);
  /* we negate the formula and show that it is unsatisfiable */
  temp = btor_not_exp (emgr, formula);
  btor_release_exp (emgr, formula);
  formula = temp;
  btor_dump_exp (emgr, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (emgr, indices[i]);
  btor_release_exp (emgr, formula);
  btor_release_exp (emgr, index);
  btor_release_exp (emgr, val);
  btor_release_exp (emgr, found);
  btor_release_exp (emgr, array);
  btor_release_exp (emgr, sorted);
  btor_release_exp (emgr, low);
  btor_release_exp (emgr, high);
  btor_release_exp (emgr, two);
  btor_release_exp (emgr, one);
  btor_delete_exp_mgr (emgr);
  free (indices);
  return 0;
}

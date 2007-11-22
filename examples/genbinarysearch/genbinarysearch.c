#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i, num_iterations;
  Btor *btor;
  BtorExp **indices, *array, *eq, *ult, *ulte, *ugt, *temp, *read1, *read2,
      *formula, *val;
  BtorExp *index, *found, *sorted, *low, *high, *two, *one, *mid, *sub, *udiv,
      *inc, *dec;
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
  btor           = btor_new_btor ();
  indices        = (BtorExp **) malloc (sizeof (BtorExp *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = btor_int_to_exp (btor, i, num_bits_index);
  array = btor_array_exp (btor, num_bits, num_bits_index);
  /* we write arbitrary search value into array at an arbitrary index */
  val   = btor_var_exp (btor, num_bits, "search_val");
  index = btor_var_exp (btor, num_bits_index, "search_index");
  temp  = btor_write_exp (btor, array, index, val);
  btor_release_exp (btor, array);
  array = temp;
  /* we assume that array is sorted */
  sorted = btor_const_exp (btor, "1");
  for (i = 0; i < num_elements - 1; i++)
  {
    read1 = btor_read_exp (btor, array, indices[i]);
    read2 = btor_read_exp (btor, array, indices[i + 1]);
    ulte  = btor_ulte_exp (btor, read1, read2);
    temp  = btor_and_exp (btor, sorted, ulte);
    btor_release_exp (btor, sorted);
    sorted = temp;
    btor_release_exp (btor, read1);
    btor_release_exp (btor, read2);
    btor_release_exp (btor, ulte);
  }
  /* binary search algorithm */
  low   = btor_int_to_exp (btor, 0, num_bits_index);
  high  = btor_int_to_exp (btor, num_elements - 1, num_bits_index);
  two   = btor_int_to_exp (btor, 2, num_bits_index);
  one   = btor_int_to_exp (btor, 1, num_bits_index);
  found = btor_const_exp (btor, "0");
  for (i = 0; i < num_iterations; i++)
  {
    /* compute mid */
    sub  = btor_sub_exp (btor, high, low);
    udiv = btor_udiv_exp (btor, sub, two);
    mid  = btor_add_exp (btor, low, udiv);
    /* read mid element */
    read1 = btor_read_exp (btor, array, mid);
    /* compare element with search val */
    eq  = btor_eq_exp (btor, val, read1);
    ult = btor_ult_exp (btor, val, read1);
    ugt = btor_ugt_exp (btor, val, read1);
    /* found element ? */
    temp = btor_or_exp (btor, found, eq);
    btor_release_exp (btor, found);
    found = temp;
    /* adapt high (if necessary) */
    dec  = btor_sub_exp (btor, mid, one);
    temp = btor_cond_exp (btor, ult, dec, high);
    btor_release_exp (btor, high);
    high = temp;
    /* adapt low (if necessary) */
    inc  = btor_add_exp (btor, mid, one);
    temp = btor_cond_exp (btor, ugt, inc, low);
    btor_release_exp (btor, low);
    low = temp;
    btor_release_exp (btor, sub);
    btor_release_exp (btor, udiv);
    btor_release_exp (btor, mid);
    btor_release_exp (btor, eq);
    btor_release_exp (btor, ult);
    btor_release_exp (btor, ugt);
    btor_release_exp (btor, read1);
    btor_release_exp (btor, inc);
    btor_release_exp (btor, dec);
  }
  /* the array is sorted implies that we have found the element */
  formula = btor_implies_exp (btor, sorted, found);
  /* we negate the formula and show that it is unsatisfiable */
  temp = btor_not_exp (btor, formula);
  btor_release_exp (btor, formula);
  formula = temp;
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) btor_release_exp (btor, indices[i]);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, index);
  btor_release_exp (btor, val);
  btor_release_exp (btor, found);
  btor_release_exp (btor, array);
  btor_release_exp (btor, sorted);
  btor_release_exp (btor, low);
  btor_release_exp (btor, high);
  btor_release_exp (btor, two);
  btor_release_exp (btor, one);
  btor_delete_btor (btor);
  free (indices);
  return 0;
}

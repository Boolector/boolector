#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"
#include "btoropt.h"
#include "utils/btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i, num_iterations;
  Btor *btor;
  BoolectorNode **indices, *array, *eq, *ult, *ulte, *ugt, *temp, *read1;
  BoolectorNode *read2, *formula, *val, *index, *found, *sorted, *low, *high;
  BoolectorNode *two, *one, *mid, *sub, *udiv, *inc, *dec;
  BoolectorSort sort_index, sort_elem, sort_array;
  if (argc != 3)
  {
    printf ("Usage: ./binarysearch <num-bits> <num-elements>\n");
    return 1;
  }
  num_bits = atoi (argv[1]);
  if (num_bits <= 0)
  {
    printf ("Number of bits must be greater than zero\n");
    return 1;
  }
  num_elements = atoi (argv[2]);
  if (num_elements < 4)
  {
    printf ("Number of elements must be at least four\n");
    return 1;
  }
  if (!btor_util_is_power_of_2 (num_elements))
  {
    printf ("Number of elements must be a power of two\n");
    return 1;
  }
  num_bits_index = btor_util_log_2 (num_elements);
  /* binary search needs log2(size(array)) + 1 iterations in the worst case */
  num_iterations = num_bits_index + 1;
  btor           = boolector_new ();
  sort_elem      = boolector_bitvec_sort (btor, num_bits);
  sort_index     = boolector_bitvec_sort (btor, num_bits_index);
  sort_array     = boolector_array_sort (btor, sort_index, sort_elem);
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
  indices = (BoolectorNode **) malloc (sizeof (BtorNode *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = boolector_int (btor, i, sort_index);
  array = boolector_array (btor, sort_array, "array");
  /* we write arbitrary search value into array at an arbitrary index */
  val   = boolector_var (btor, sort_elem, "search_val");
  index = boolector_var (btor, sort_index, "search_index");
  temp  = boolector_write (btor, array, index, val);
  boolector_release (btor, array);
  array = temp;
  /* we assume that array is sorted */
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
  /* binary search algorithm */
  low   = boolector_int (btor, 0, sort_index);
  high  = boolector_int (btor, num_elements - 1, sort_index);
  two   = boolector_int (btor, 2, sort_index);
  one   = boolector_int (btor, 1, sort_index);
  found = boolector_const (btor, "0");
  for (i = 0; i < num_iterations; i++)
  {
    /* compute mid */
    sub  = boolector_sub (btor, high, low);
    udiv = boolector_udiv (btor, sub, two);
    mid  = boolector_add (btor, low, udiv);
    /* read mid element */
    read1 = boolector_read (btor, array, mid);
    /* compare element with search val */
    eq  = boolector_eq (btor, val, read1);
    ult = boolector_ult (btor, val, read1);
    ugt = boolector_ugt (btor, val, read1);
    /* found element ? */
    temp = boolector_or (btor, found, eq);
    boolector_release (btor, found);
    found = temp;
    /* adapt high (if necessary) */
    dec  = boolector_sub (btor, mid, one);
    temp = boolector_cond (btor, ult, dec, high);
    boolector_release (btor, high);
    high = temp;
    /* adapt low (if necessary) */
    inc  = boolector_add (btor, mid, one);
    temp = boolector_cond (btor, ugt, inc, low);
    boolector_release (btor, low);
    low = temp;
    boolector_release (btor, sub);
    boolector_release (btor, udiv);
    boolector_release (btor, mid);
    boolector_release (btor, eq);
    boolector_release (btor, ult);
    boolector_release (btor, ugt);
    boolector_release (btor, read1);
    boolector_release (btor, inc);
    boolector_release (btor, dec);
  }
  /* the array is sorted implies that we have found the element */
  formula = boolector_implies (btor, sorted, found);
  /* we negate the formula and show that it is unsatisfiable */
  temp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = temp;
  boolector_dump_btor_node (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) boolector_release (btor, indices[i]);
  boolector_release (btor, formula);
  boolector_release (btor, index);
  boolector_release (btor, val);
  boolector_release (btor, found);
  boolector_release (btor, array);
  boolector_release (btor, sorted);
  boolector_release (btor, low);
  boolector_release (btor, high);
  boolector_release (btor, two);
  boolector_release (btor, one);
  boolector_release_sort (btor, sort_index);
  boolector_release_sort (btor, sort_elem);
  boolector_release_sort (btor, sort_array);
  boolector_delete (btor);
  free (indices);
  return 0;
}

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"

#define ARRAY1_EXAMPLE_ELEM_BW 8
#define ARRAY1_EXAMPLE_INDEX_BW 3
#define ARRAY1_EXAMPLE_ARRAY_SIZE (1 << ARRAY1_EXAMPLE_INDEX_BW)

/* We verify the following linear search algorithm. We iterate over an array
 * and compute a maximum value as the following pseudo code shows:
 *
 * unsigned int array[ARRAY_SIZE];
 * unsigned int max;
 * int i;
 * ...
 * max = array[0];
 * for (i = 1; i < ARRAY_SIZE; i++)
 *   if (array[i] > max)
 *     max = array[i]
 *
 * Finally, we prove that it is not possible to find an array position
 * such that the value stored at this position is greater than 'max'.
 * If we can show this, we have proved that this algorithm indeed finds
 * a maximum value. Note that we prove that the algorithm finds an
 * arbitrary maximum (multiple maxima are possible), not necessarily
 * the first maximum.
 */

int
main (void)
{
  Btor *btor;
  BoolectorNode *array, *read, *max, *temp, *ugt, *formula, *index;
  BoolectorNode *indices[ARRAY1_EXAMPLE_ARRAY_SIZE];
  BoolectorSort sort_elem, sort_index, sort_array;
  int i, result;

  btor       = boolector_new ();
  sort_index = boolector_bitvec_sort (btor, ARRAY1_EXAMPLE_INDEX_BW);
  sort_elem  = boolector_bitvec_sort (btor, ARRAY1_EXAMPLE_ELEM_BW);
  sort_array = boolector_array_sort (btor, sort_index, sort_elem);

  /* We create all possible constants that are used as read indices */
  for (i = 0; i < ARRAY1_EXAMPLE_ARRAY_SIZE; i++)
    indices[i] = boolector_int (btor, i, sort_index);

  array = boolector_array (btor, sort_array, 0);
  /* Current maximum is first element of array */
  max = boolector_read (btor, array, indices[0]);
  /* Symbolic loop unrolling */
  for (i = 1; i < ARRAY1_EXAMPLE_ARRAY_SIZE; i++)
  {
    read = boolector_read (btor, array, indices[i]);
    ugt  = boolector_ugt (btor, read, max);
    /* found a new maximum? */
    temp = boolector_cond (btor, ugt, read, max);
    boolector_release (btor, max);
    max = temp;
    boolector_release (btor, read);
    boolector_release (btor, ugt);
  }

  /* Now we show that 'max' is indeed a maximum */
  /* We read at an arbitrary position */
  index = boolector_var (btor, sort_index, NULL);
  read  = boolector_read (btor, array, index);

  /* We assume that it is possible that the read value is greater than 'max' */
  formula = boolector_ugt (btor, read, max);

  /* We assert the formula and call Boolector */
  boolector_assert (btor, formula);
  result = boolector_sat (btor);
  printf ("Expect: unsat\n");
  printf ("Boolector: %s\n",
          result == BOOLECTOR_SAT
              ? "sat"
              : (result == BOOLECTOR_UNSAT ? "unsat" : "unknown"));
  if (result != BOOLECTOR_UNSAT) abort ();

  /* clean up */
  for (i = 0; i < ARRAY1_EXAMPLE_ARRAY_SIZE; i++)
    boolector_release (btor, indices[i]);
  boolector_release (btor, formula);
  boolector_release (btor, read);
  boolector_release (btor, index);
  boolector_release (btor, max);
  boolector_release (btor, array);
  boolector_release_sort (btor, sort_array);
  boolector_release_sort (btor, sort_index);
  boolector_release_sort (btor, sort_elem);
  assert (boolector_get_refs (btor) == 0);
  boolector_delete (btor);
  return 0;
}

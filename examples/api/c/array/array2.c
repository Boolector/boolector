#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"
#include "btoropt.h"

#define ARRAY2_EXAMPLE_ELEM_BW 8
#define ARRAY2_EXAMPLE_INDEX_BW 1

/* We demonstrate Boolector's ability to obtain Array models.
 * We check the following formula for satisfiability:
 * write (array1, 0, 3) = write (array2, 1, 5)
 */

int
main (void)
{
  Btor *btor;
  BoolectorNode *array1, *array2, *zero, *one, *val1, *val2;
  BoolectorNode *write1, *write2, *formula;
  BoolectorSort sort_index, sort_elem, sort_array;
  char **indices, **values;
  int32_t result;
  uint32_t i, size;

  btor       = boolector_new ();
  sort_index = boolector_bitvec_sort (btor, ARRAY2_EXAMPLE_INDEX_BW);
  sort_elem  = boolector_bitvec_sort (btor, ARRAY2_EXAMPLE_ELEM_BW);
  sort_array = boolector_array_sort (btor, sort_index, sort_elem);
  boolector_set_opt (btor, BTOR_OPT_MODEL_GEN, 1);

  zero   = boolector_zero (btor, sort_index);
  one    = boolector_one (btor, sort_index);
  val1   = boolector_int (btor, 3, sort_elem);
  val2   = boolector_int (btor, 5, sort_elem);
  array1 = boolector_array (btor, sort_array, 0);
  array2 = boolector_array (btor, sort_array, 0);
  write1 = boolector_write (btor, array1, zero, val1);
  write2 = boolector_write (btor, array2, one, val2);
  /* Note: we compare two arrays for equality ---> needs extensional theory */
  formula = boolector_eq (btor, write1, write2);
  boolector_assert (btor, formula);
  result = boolector_sat (btor);
  printf ("Expect: sat\n");
  printf ("Boolector: %s\n",
          result == BOOLECTOR_SAT
              ? "sat"
              : (result == BOOLECTOR_UNSAT ? "unsat" : "unknown"));
  if (result != BOOLECTOR_SAT) abort ();

  printf ("\nModel:\n");
  /* Formula is satisfiable, we can obtain array models: */
  boolector_array_assignment (btor, array1, &indices, &values, &size);
  if (size > 0)
  {
    printf ("Array1:\n");
    for (i = 0; i < size; i++)
      printf ("Array1[%s] = %s\n", indices[i], values[i]);
    boolector_free_array_assignment (btor, indices, values, size);
  }

  boolector_array_assignment (btor, array2, &indices, &values, &size);
  if (size > 0)
  {
    printf ("\nArray2:\n");
    for (i = 0; i < size; i++)
      printf ("Array2[%s] = %s\n", indices[i], values[i]);
    boolector_free_array_assignment (btor, indices, values, size);
  }

  boolector_array_assignment (btor, write1, &indices, &values, &size);
  if (size > 0)
  {
    printf ("\nWrite1:\n");
    for (i = 0; i < size; i++)
      printf ("Write1[%s] = %s\n", indices[i], values[i]);
    boolector_free_array_assignment (btor, indices, values, size);
  }

  boolector_array_assignment (btor, write2, &indices, &values, &size);
  if (size > 0)
  {
    printf ("\nWrite2:\n");
    for (i = 0; i < size; i++)
      printf ("Write2[%s] = %s\n", indices[i], values[i]);
    boolector_free_array_assignment (btor, indices, values, size);
  }

  /* clean up */
  boolector_release (btor, formula);
  boolector_release (btor, write1);
  boolector_release (btor, write2);
  boolector_release (btor, array1);
  boolector_release (btor, array2);
  boolector_release (btor, val1);
  boolector_release (btor, val2);
  boolector_release (btor, zero);
  boolector_release (btor, one);
  boolector_release_sort (btor, sort_array);
  boolector_release_sort (btor, sort_index);
  boolector_release_sort (btor, sort_elem);
  assert (boolector_get_refs (btor) == 0);
  boolector_delete (btor);
  return 0;
}

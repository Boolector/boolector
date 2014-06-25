#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"

#define ARRAY2_EXAMPLE_VALUE_BW 8
#define ARRAY2_EXAMPLE_INDEX_BW 1

/* We demonstrate Boolector's ability to obtain Array models.
 * We check the following formula for satisfiability:
 * write (array1, 0, 3) = write (array2, 1, 5)
 */

int
main (void)
{
  Btor *btor;
  BtorNode *array1, *array2, *zero, *one, *val1, *val2;
  BtorNode *write1, *write2, *formula;
  char **indices, **values;
  int result, size, i;

  btor = boolector_new ();
  boolector_set_opt_model_gen (btor, 1);

  zero   = boolector_zero (btor, ARRAY2_EXAMPLE_INDEX_BW);
  one    = boolector_one (btor, ARRAY2_EXAMPLE_INDEX_BW);
  val1   = boolector_int (btor, 3, ARRAY2_EXAMPLE_VALUE_BW);
  val2   = boolector_int (btor, 5, ARRAY2_EXAMPLE_VALUE_BW);
  array1 = boolector_array (
      btor, ARRAY2_EXAMPLE_VALUE_BW, ARRAY2_EXAMPLE_INDEX_BW, NULL);
  array2 = boolector_array (
      btor, ARRAY2_EXAMPLE_VALUE_BW, ARRAY2_EXAMPLE_INDEX_BW, NULL);
  write1 = boolector_write (btor, array1, zero, val1);
  write2 = boolector_write (btor, array2, one, val2);
  /* Note: we compare two arrays for equality ---> needs extensional theory */
  formula = boolector_eq (btor, write1, write2);
  boolector_assert (btor, formula);
  result = boolector_sat (btor);
  if (result == BOOLECTOR_SAT)
    printf ("Formula is satisfiable\n");
  else
    abort ();

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
  assert (boolector_get_refs (btor) == 0);
  boolector_delete (btor);
  return 0;
}

#include <assert.h>
#include <limits.h>
#include "boolector.h"
#include "btoropt.h"

#define ARRAY3_EXAMPLE_ELEM_BW 8
#define ARRAY3_EXAMPLE_INDEX_BW 1

int
main ()
{
  int sat_result;
  BoolectorNode *array, *index1, *index2, *read1, *read2, *eq, *ne;
  BoolectorSort sort_index, sort_elem, sort_array;
  Btor *btor;

  btor       = boolector_new ();
  sort_index = boolector_bitvec_sort (btor, ARRAY3_EXAMPLE_INDEX_BW);
  sort_elem  = boolector_bitvec_sort (btor, ARRAY3_EXAMPLE_ELEM_BW);
  sort_array = boolector_array_sort (btor, sort_index, sort_elem);
  boolector_set_opt (btor, BTOR_OPT_INCREMENTAL, 1);

  array  = boolector_array (btor, sort_array, 0);
  index1 = boolector_var (btor, sort_index, 0);
  index2 = boolector_var (btor, sort_index, 0);
  read1  = boolector_read (btor, array, index1);
  read2  = boolector_read (btor, array, index2);
  eq     = boolector_eq (btor, index1, index2);
  ne     = boolector_ne (btor, read1, read2);

  /* we enforce that index1 is equal to index 2 */
  boolector_assert (btor, eq);
  sat_result = boolector_sat (btor);
  assert (sat_result == BOOLECTOR_SAT);
  /* now we additionally assume that the read values differ
   * the instance is now unsatasfiable as read congruence is violated */
  boolector_assume (btor, ne);
  sat_result = boolector_sat (btor);
  assert (sat_result == BOOLECTOR_UNSAT);
  /* after the SAT call the assumptions are gone
   * the instance is now satisfiable again */
  sat_result = boolector_sat (btor);
  assert (sat_result == BOOLECTOR_SAT);
  boolector_release (btor, array);
  boolector_release (btor, index1);
  boolector_release (btor, index2);
  boolector_release (btor, read1);
  boolector_release (btor, read2);
  boolector_release (btor, eq);
  boolector_release (btor, ne);
  boolector_release_sort (btor, sort_array);
  boolector_release_sort (btor, sort_index);
  boolector_release_sort (btor, sort_elem);
  boolector_delete (btor);
  return 0;
}

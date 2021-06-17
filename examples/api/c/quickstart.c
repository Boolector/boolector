#include "boolector.h"

int
main ()
{
  // Create Boolector instance
  Btor *btor = boolector_new ();
  // Enable model generation
  boolector_set_opt (btor, BTOR_OPT_MODEL_GEN, 1);

  // Create bit-vector sort of size 8
  BoolectorSort bvsort8 = boolector_bitvec_sort (btor, 8);

  // Create expressions
  BoolectorNode *x       = boolector_var (btor, bvsort8, "x");
  BoolectorNode *y       = boolector_var (btor, bvsort8, "y");
  BoolectorNode *zero    = boolector_zero (btor, bvsort8);
  BoolectorNode *hundred = boolector_int (btor, 100, bvsort8);

  // 0 < x
  BoolectorNode *ult_x = boolector_ult (btor, zero, x);
  boolector_assert (btor, ult_x);

  // x <= 100
  BoolectorNode *ulte_x = boolector_ulte (btor, x, hundred);
  boolector_assert (btor, ulte_x);

  // 0 < y
  BoolectorNode *ult_y = boolector_ult (btor, zero, y);
  boolector_assert (btor, ult_y);

  // y <= 100
  BoolectorNode *ulte_y = boolector_ulte (btor, y, hundred);
  boolector_assert (btor, ulte_y);

  // x * y
  BoolectorNode *mul = boolector_mul (btor, x, y);

  // x * y < 100
  BoolectorNode *ult = boolector_ult (btor, mul, hundred);
  boolector_assert (btor, ult);
  BoolectorNode *umulo  = boolector_umulo (btor, x, y);
  BoolectorNode *numulo = boolector_not (btor, umulo);  // prevent overflow
  boolector_assert (btor, numulo);

  int result = boolector_sat (btor);
  printf ("Expect: sat\n");
  printf ("Boolector: ");
  if (result == BOOLECTOR_SAT)
  {
    printf ("sat\n");
  }
  else if (result == BOOLECTOR_UNSAT)
  {
    printf ("unsat\n");
  }
  else
  {
    printf ("unknown\n");
  }
  printf ("\n");

  // Get assignment strings for x and y
  const char *xstr = boolector_bv_assignment (btor, x);  // returns "00000100"
  const char *ystr = boolector_bv_assignment (btor, y);  // returns "00010101"
  printf ("assignment of x: %s\n", xstr);
  printf ("assignment of y: %s\n", ystr);
  printf ("\n");

  // Alternatively, get values for x and y as nodes
  BoolectorNode *x_value = boolector_get_value(btor, x);
  BoolectorNode *y_value = boolector_get_value(btor, y);
  const char *xvaluestr =
      boolector_bv_assignment (btor, x_value);  // returns "00000100"
  const char *yvaluestr =
      boolector_bv_assignment (btor, y_value);  // returns "00010101"
  printf ("assignment of x (via get-value): %s\n", xvaluestr);
  printf ("assignment of y (via get-value): %s\n", yvaluestr);
  printf ("\n");

  printf ("Print model in BTOR format:\n");
  boolector_print_model (btor, "btor", stdout);
  printf ("\n");
  printf ("Print model in SMT-LIBv2 format:\n");
  boolector_print_model (btor, "smt2", stdout);
  printf ("\n");

  // Release expressions
  boolector_release (btor, x);
  boolector_release (btor, y);
  boolector_release (btor, zero);
  boolector_release (btor, hundred);
  boolector_release (btor, ult_x);
  boolector_release (btor, ulte_x);
  boolector_release (btor, ult_y);
  boolector_release (btor, ulte_y);
  boolector_release (btor, mul);
  boolector_release (btor, ult);
  boolector_release (btor, numulo);
  boolector_release (btor, umulo);

  // Release assigments
  boolector_free_bv_assignment (btor, xstr);
  boolector_free_bv_assignment (btor, ystr);

  // Release sorts
  boolector_release_sort (btor, bvsort8);

  // Delete Boolector instance
  boolector_delete (btor);
}

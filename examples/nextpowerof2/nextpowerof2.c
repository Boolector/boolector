#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"
#include "btoropt.h"
#include "utils/btorutil.h"

/* We verifiy that the next power of 2 algorithm
 * from the book "hacker's delight" (Warren Jr., Henry)
 * works as expected, e.g. next_power_of_2(5) == 8
 *
 * int next_power_of_2 (int x)
 * {
 *   int i;
 *   x--;
 *   for (i = 1; i < sizeof(int) * 8; i = i * 2)
 *     x = x | (x >> i)
 *   return x + 1;
 * }
 */

int
main (int argc, char **argv)
{
  int i, num_bits, num_bits_log_2;
  Btor *btor;
  BoolectorNode *formula, *next_power, *next_smallest_power, *one, *temp;
  BoolectorNode *shift, *cur_const, *x, *eq, *gte, *lte, *gt;
  BoolectorNode **powers;
  BoolectorSort s0, s1;
  char *const_string;
  if (argc != 2)
  {
    printf ("Usage: ./nextpowerof2 <num-bits>\n");
    return EXIT_FAILURE;
  }
  num_bits = atoi (argv[1]);
  if (num_bits <= 1)
  {
    printf ("Number of bits must be greater than one\n");
    return EXIT_FAILURE;
  }
  if (!btor_util_is_power_of_2 (num_bits))
  {
    printf ("Number of bits must be a power of 2\n");
    return EXIT_FAILURE;
  }

  num_bits_log_2 = btor_util_log_2 (num_bits);

  powers = (BoolectorNode **) malloc (sizeof (BoolectorNode *) * num_bits);
  const_string           = (char *) malloc (sizeof (char) * (num_bits + 1));
  const_string[num_bits] = '\0';
  btor                   = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
  for (i = 0; i < num_bits; i++) const_string[i] = '0';
  for (i = 0; i < num_bits; i++)
  {
    const_string[num_bits - 1 - i] = '1';
    powers[i]                      = boolector_const (btor, const_string);
    const_string[num_bits - 1 - i] = '0';
  }
  s0  = boolector_bitvec_sort (btor, num_bits);
  s1  = boolector_bitvec_sort (btor, num_bits_log_2);
  one = boolector_unsigned_int (btor, 1, s0);
  x   = boolector_var (btor, s0, "x");

  next_power = boolector_sub (btor, x, one);
  for (i = 1; i < num_bits; i++)
  {
    cur_const = boolector_unsigned_int (btor, i, s1);
    shift     = boolector_sra (btor, next_power, cur_const);
    temp      = boolector_or (btor, next_power, shift);
    boolector_release (btor, next_power);
    next_power = temp;
    boolector_release (btor, shift);
    boolector_release (btor, cur_const);
  }
  temp = boolector_add (btor, next_power, one);
  boolector_release (btor, next_power);
  next_power = temp;
  formula    = boolector_false (btor);
  for (i = 0; i < num_bits; i++)
  {
    eq   = boolector_eq (btor, next_power, powers[i]);
    temp = boolector_or (btor, formula, eq);
    boolector_release (btor, formula);
    formula = temp;
    boolector_release (btor, eq);
  }

  /* x must be less than next_power,
   * we take unsigned less than, as the biggest power of 2 is INT_MIN,
   * and therefore negative.
   */
  lte  = boolector_ulte (btor, x, next_power);
  temp = boolector_and (btor, lte, formula);
  boolector_release (btor, formula);
  formula = temp;

  /* we show that x is greater than (next_power >> 1), hence next_power
   * is indeed the NEXT biggest power of 2 */
  cur_const           = boolector_unsigned_int (btor, 1, s1);
  next_smallest_power = boolector_srl (btor, next_power, cur_const);
  gt                  = boolector_sgt (btor, x, next_smallest_power);
  temp                = boolector_and (btor, gt, formula);
  boolector_release (btor, formula);
  formula = temp;

  /* we assume x > 0 */
  gte  = boolector_sgte (btor, x, one);
  temp = boolector_implies (btor, gte, formula);
  boolector_release (btor, formula);
  formula = temp;

  /* we show that negation is unsatisfiable to verify the algorithm */
  temp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = temp;
  boolector_dump_btor_node (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_bits; i++) boolector_release (btor, powers[i]);
  boolector_release (btor, lte);
  boolector_release (btor, gte);
  boolector_release (btor, gt);
  boolector_release (btor, cur_const);
  boolector_release (btor, next_smallest_power);
  boolector_release (btor, formula);
  boolector_release (btor, next_power);
  boolector_release (btor, x);
  boolector_release (btor, one);
  boolector_release_sort (btor, s0);
  boolector_release_sort (btor, s1);
  boolector_delete (btor);
  free (powers);
  free (const_string);
  return 0;
}

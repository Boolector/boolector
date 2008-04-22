#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

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
  BtorExp *formula, *next_power, *next_smallest_power, *one, *temp;
  BtorExp *shift, *cur_const, *x, *eq, *gte, *lte, *gt;
  BtorExp **powers;
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
  if (!btor_is_power_of_2_util (num_bits))
  {
    printf ("Number of bits must be a power of 2\n");
    return EXIT_FAILURE;
  }

  num_bits_log_2 = btor_log_2_util (num_bits);

  powers                 = (BtorExp **) malloc (sizeof (BtorExp *) * num_bits);
  const_string           = (char *) malloc (sizeof (char) * (num_bits + 1));
  const_string[num_bits] = '\0';
  btor                   = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);
  for (i = 0; i < num_bits; i++) const_string[i] = '0';
  for (i = 0; i < num_bits; i++)
  {
    const_string[num_bits - 1 - i] = '1';
    powers[i]                      = btor_const_exp (btor, const_string);
    const_string[num_bits - 1 - i] = '0';
  }
  one = btor_unsigned_to_exp (btor, 1, num_bits);
  x   = btor_var_exp (btor, num_bits, "x");

  next_power = btor_sub_exp (btor, x, one);
  for (i = 1; i < num_bits; i++)
  {
    cur_const = btor_unsigned_to_exp (btor, i, num_bits_log_2);
    shift     = btor_sra_exp (btor, next_power, cur_const);
    temp      = btor_or_exp (btor, next_power, shift);
    btor_release_exp (btor, next_power);
    next_power = temp;
    btor_release_exp (btor, shift);
    btor_release_exp (btor, cur_const);
  }
  temp = btor_add_exp (btor, next_power, one);
  btor_release_exp (btor, next_power);
  next_power = temp;
  formula    = btor_false_exp (btor);
  for (i = 0; i < num_bits; i++)
  {
    eq   = btor_eq_exp (btor, next_power, powers[i]);
    temp = btor_or_exp (btor, formula, eq);
    btor_release_exp (btor, formula);
    formula = temp;
    btor_release_exp (btor, eq);
  }

  /* x must be less than next_power,
   * we take unsigned less than, as the biggest power of 2 is INT_MIN,
   * and therefore negative.
   */
  lte  = btor_ulte_exp (btor, x, next_power);
  temp = btor_and_exp (btor, lte, formula);
  btor_release_exp (btor, formula);
  formula = temp;

  /* we show that x is greater than (next_power >> 1), hence next_power
   * is indeed the NEXT biggest power of 2 */
  cur_const           = btor_unsigned_to_exp (btor, 1, num_bits_log_2);
  next_smallest_power = btor_srl_exp (btor, next_power, cur_const);
  gt                  = btor_sgt_exp (btor, x, next_smallest_power);
  temp                = btor_and_exp (btor, gt, formula);
  btor_release_exp (btor, formula);
  formula = temp;

  /* we assume x > 0 */
  gte  = btor_sgte_exp (btor, x, one);
  temp = btor_implies_exp (btor, gte, formula);
  btor_release_exp (btor, formula);
  formula = temp;

  /* we show that negation is unsatisfiable to verify the algorithm */
  temp = btor_not_exp (btor, formula);
  btor_release_exp (btor, formula);
  formula = temp;
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_bits; i++) btor_release_exp (btor, powers[i]);
  btor_release_exp (btor, lte);
  btor_release_exp (btor, gte);
  btor_release_exp (btor, gt);
  btor_release_exp (btor, cur_const);
  btor_release_exp (btor, next_smallest_power);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, next_power);
  btor_release_exp (btor, x);
  btor_release_exp (btor, one);
  btor_delete_btor (btor);
  free (powers);
  free (const_string);
  return 0;
}

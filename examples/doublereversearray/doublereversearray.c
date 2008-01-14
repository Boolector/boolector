#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../boolector.h"

static int
number_of_chars_int (int x)
{
  int result;
  assert (x > 0);
  result = 0;
  while (x > 0)
  {
    result++;
    x /= 10;
  }
  return result;
}

static BtorExp *
reverse_array_mem_xor (Btor *btor,
                       BtorExp *mem,
                       int num_elements,
                       BtorExp *start)
{
  BtorExp *num_elements_m_1_exp, *one, *bottom_exp, *top_exp;
  BtorExp *temp, *result, *x, *y, *xor;
  int top, bottom;
  assert (btor != NULL);
  assert (mem != NULL);
  assert (num_elements > 0);
  assert (start != NULL);

  result               = mem;
  num_elements_m_1_exp = btor_unsigned_to_exp (btor, num_elements - 1, 32);
  one                  = btor_one_exp (btor, 32);
  bottom_exp           = btor_copy_exp (btor, start);
  bottom               = 0;
  top_exp              = btor_add_exp (btor, start, num_elements_m_1_exp);
  top                  = num_elements - 1;
  while (top > bottom)
  {
    x    = btor_read_exp (btor, result, bottom_exp);
    y    = btor_read_exp (btor, result, top_exp);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, bottom_exp, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, x);
    btor_release_exp (btor, xor);

    x    = btor_read_exp (btor, result, bottom_exp);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, top_exp, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, y);
    btor_release_exp (btor, xor);

    y    = btor_read_exp (btor, result, top_exp);
    xor  = btor_xor_exp (btor, x, y);
    temp = btor_write_exp (btor, result, bottom_exp, xor);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, x);
    btor_release_exp (btor, y);
    btor_release_exp (btor, xor);

    top--;
    temp = btor_sub_exp (btor, top_exp, one);
    btor_release_exp (btor, top_exp);
    top_exp = temp;

    bottom++;
    temp = btor_add_exp (btor, bottom_exp, one);
    btor_release_exp (btor, bottom_exp);
    bottom_exp = temp;
  }

  btor_release_exp (btor, one);
  btor_release_exp (btor, num_elements_m_1_exp);
  btor_release_exp (btor, top_exp);
  btor_release_exp (btor, bottom_exp);
  return result;
}

static BtorExp *
reverse_array_mem (Btor *btor, BtorExp *mem, int num_elements, BtorExp *start)
{
  BtorExp *num_elements_m_1_exp, *one, *bottom_exp, *top_exp;
  BtorExp *temp, *result, *x, *y;
  int top, bottom;
  assert (btor != NULL);
  assert (mem != NULL);
  assert (num_elements > 0);
  assert (start != NULL);

  result               = mem;
  num_elements_m_1_exp = btor_unsigned_to_exp (btor, num_elements - 1, 32);
  one                  = btor_one_exp (btor, 32);
  bottom_exp           = btor_copy_exp (btor, start);
  bottom               = 0;
  top_exp              = btor_add_exp (btor, start, num_elements_m_1_exp);
  top                  = num_elements - 1;
  while (top > bottom)
  {
    x = btor_read_exp (btor, result, bottom_exp);
    y = btor_read_exp (btor, result, top_exp);

    temp = btor_write_exp (btor, result, top_exp, x);
    btor_release_exp (btor, result);
    result = temp;

    temp = btor_write_exp (btor, result, bottom_exp, y);
    btor_release_exp (btor, result);
    result = temp;

    top--;
    temp = btor_sub_exp (btor, top_exp, one);
    btor_release_exp (btor, top_exp);
    top_exp = temp;

    bottom++;
    temp = btor_add_exp (btor, bottom_exp, one);
    btor_release_exp (btor, bottom_exp);
    bottom_exp = temp;

    btor_release_exp (btor, x);
    btor_release_exp (btor, y);
  }

  btor_release_exp (btor, one);
  btor_release_exp (btor, num_elements_m_1_exp);
  btor_release_exp (btor, top_exp);
  btor_release_exp (btor, bottom_exp);
  return result;
}

int
main (int argc, char **argv)
{
  int num_elements, i;
  char *string;
  Btor *btor;
  BtorExp *mem1, *mem2, *orig_mem, *formula, *start;
  if (argc != 2)
  {
    printf ("Usage: ./reversearraymemxor <num-elements>\n");
    return 1;
  }
  num_elements = atoi (argv[1]);
  if (num_elements <= 0)
  {
    printf ("Number of elements must be greater than zero\n");
    return 1;
  }

  btor = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);

  orig_mem = btor_array_exp (btor, 8, 32);
  mem1     = btor_copy_exp (btor, orig_mem);
  mem2     = btor_copy_exp (btor, orig_mem);
  for (i = 0; i < num_elements; i++)
  {
    string = (char *) malloc (
        sizeof (char) * (strlen ("start") + number_of_chars_int (i + 1) + 1));
    sprintf (string, "start%d", i + 1);
    start = btor_var_exp (btor, 32, string);
    mem1  = reverse_array_mem (btor, mem1, num_elements, start);
    mem2  = reverse_array_mem_xor (btor, mem2, num_elements, start);
    btor_release_exp (btor, start);
    free (string);
  }
  /* memory has to be equal */
  /* we show this by showing that the negation is unsat */
  formula = btor_ne_exp (btor, mem1, mem2);
  btor_dump_exp (btor, stdout, formula);
  /* clean up */
  btor_release_exp (btor, formula);
  btor_release_exp (btor, mem1);
  btor_release_exp (btor, mem2);
  btor_release_exp (btor, orig_mem);
  btor_delete_btor (btor);
  return 0;
}

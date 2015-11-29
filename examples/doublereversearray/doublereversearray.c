#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "boolector.h"
#include "utils/btorutil.h"

static BoolectorNode *
reverse_array_mem_xor (Btor *btor,
                       BoolectorNode *mem,
                       int num_elements,
                       BoolectorNode *start)
{
  BoolectorNode *num_elements_m_1, *one, *bottom_exp, *top_exp;
  BoolectorNode *temp, *result, *x, *y, *xor;
  int top, bottom;
  assert (btor != NULL);
  assert (mem != NULL);
  assert (num_elements > 0);
  assert (start != NULL);

  result           = mem;
  num_elements_m_1 = boolector_unsigned_int (btor, num_elements - 1, 32);
  one              = boolector_one (btor, 32);
  bottom_exp       = boolector_copy (btor, start);
  bottom           = 0;
  top_exp          = boolector_add (btor, start, num_elements_m_1);
  top              = num_elements - 1;
  while (top > bottom)
  {
    x    = boolector_read (btor, result, bottom_exp);
    y    = boolector_read (btor, result, top_exp);
    xor  = boolector_xor (btor, x, y);
    temp = boolector_write (btor, result, bottom_exp, xor);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, x);
    boolector_release (btor, xor);

    x    = boolector_read (btor, result, bottom_exp);
    xor  = boolector_xor (btor, x, y);
    temp = boolector_write (btor, result, top_exp, xor);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, y);
    boolector_release (btor, xor);

    y    = boolector_read (btor, result, top_exp);
    xor  = boolector_xor (btor, x, y);
    temp = boolector_write (btor, result, bottom_exp, xor);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, x);
    boolector_release (btor, y);
    boolector_release (btor, xor);

    top--;
    temp = boolector_sub (btor, top_exp, one);
    boolector_release (btor, top_exp);
    top_exp = temp;

    bottom++;
    temp = boolector_add (btor, bottom_exp, one);
    boolector_release (btor, bottom_exp);
    bottom_exp = temp;
  }

  boolector_release (btor, one);
  boolector_release (btor, num_elements_m_1);
  boolector_release (btor, top_exp);
  boolector_release (btor, bottom_exp);
  return result;
}

static BoolectorNode *
reverse_array_mem (Btor *btor,
                   BoolectorNode *mem,
                   int num_elements,
                   BoolectorNode *start)
{
  BoolectorNode *num_elements_m_1, *one, *bottom_exp, *top_exp;
  BoolectorNode *temp, *result, *x, *y;
  int top, bottom;
  assert (btor != NULL);
  assert (mem != NULL);
  assert (num_elements > 0);
  assert (start != NULL);

  result           = mem;
  num_elements_m_1 = boolector_unsigned_int (btor, num_elements - 1, 32);
  one              = boolector_one (btor, 32);
  bottom_exp       = boolector_copy (btor, start);
  bottom           = 0;
  top_exp          = boolector_add (btor, start, num_elements_m_1);
  top              = num_elements - 1;
  while (top > bottom)
  {
    x = boolector_read (btor, result, bottom_exp);
    y = boolector_read (btor, result, top_exp);

    temp = boolector_write (btor, result, top_exp, x);
    boolector_release (btor, result);
    result = temp;

    temp = boolector_write (btor, result, bottom_exp, y);
    boolector_release (btor, result);
    result = temp;

    top--;
    temp = boolector_sub (btor, top_exp, one);
    boolector_release (btor, top_exp);
    top_exp = temp;

    bottom++;
    temp = boolector_add (btor, bottom_exp, one);
    boolector_release (btor, bottom_exp);
    bottom_exp = temp;

    boolector_release (btor, x);
    boolector_release (btor, y);
  }

  boolector_release (btor, one);
  boolector_release (btor, num_elements_m_1);
  boolector_release (btor, top_exp);
  boolector_release (btor, bottom_exp);
  return result;
}

int
main (int argc, char **argv)
{
  int num_elements, i;
  char *string;
  Btor *btor;
  BoolectorNode *mem1, *mem2, *orig_mem, *formula, *start;
  if (argc != 2)
  {
    printf ("Usage: ./doublereversearray <num-elements>\n");
    return 1;
  }
  num_elements = atoi (argv[1]);
  if (num_elements <= 0)
  {
    printf ("Number of elements must be greater than zero\n");
    return 1;
  }

  btor = boolector_new ();
  boolector_set_opt (btor, "rewrite_level", 0);

  orig_mem = boolector_array (btor, 8, 32, "mem");
  mem1     = boolector_copy (btor, orig_mem);
  mem2     = boolector_copy (btor, orig_mem);
  for (i = 0; i < num_elements; i++)
  {
    string = (char *) malloc (
        sizeof (char) * (strlen ("start") + btor_num_digits_util (i + 1) + 1));
    sprintf (string, "start%d", i + 1);
    start = boolector_var (btor, 32, string);
    mem1  = reverse_array_mem (btor, mem1, num_elements, start);
    mem2  = reverse_array_mem_xor (btor, mem2, num_elements, start);
    boolector_release (btor, start);
    free (string);
  }
  /* memory has to be equal */
  /* we show this by showing that the negation is unsat */
  formula = boolector_ne (btor, mem1, mem2);
  boolector_dump_btor_node (btor, stdout, formula);
  /* clean up */
  boolector_release (btor, formula);
  boolector_release (btor, mem1);
  boolector_release (btor, mem2);
  boolector_release (btor, orig_mem);
  boolector_delete (btor);
  return 0;
}

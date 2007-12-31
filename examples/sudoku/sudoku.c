#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

#define SUDOKU_NUM_BITS_INDEX 7
#define SUDOKU_NUM_BITS_VAL 4
#define SUDOKU_SIZE 9
#define SUDOKU_NUM_FIELDS (SUDOKU_SIZE * SUDOKU_SIZE)

BtorExp **indices, **values;

static BtorExp *
generate_row_constraint (Btor *btor, BtorExp *matrix, int line)
{
  int i, j;
  BtorExp *result, *temp, *read_i, *read_j, *ne, *lte, *gt, *and;
  assert (btor != NULL);
  assert (matrix != NULL);
  assert (line >= 0);
  assert (line < SUDOKU_SIZE);
  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    read_i = btor_read_exp (btor, matrix, indices[line * SUDOKU_SIZE + i]);
    gt     = btor_ugt_exp (btor, read_i, values[0]);
    lte    = btor_ulte_exp (btor, read_i, values[9]);
    and    = btor_and_exp (btor, lte, gt);
    temp   = btor_and_exp (btor, result, and);
    btor_release_exp (btor, result);
    result = temp;
    for (j = i + 1; j < SUDOKU_SIZE; j++)
    {
      read_j = btor_read_exp (btor, matrix, indices[line * SUDOKU_SIZE + j]);
      ne     = btor_ne_exp (btor, read_i, read_j);
      temp   = btor_and_exp (btor, result, ne);
      btor_release_exp (btor, result);
      result = temp;
      btor_release_exp (btor, ne);
      btor_release_exp (btor, read_j);
    }
    btor_release_exp (btor, read_i);
    btor_release_exp (btor, gt);
    btor_release_exp (btor, lte);
    btor_release_exp (btor, and);
  }
  return result;
}

static BtorExp *
generate_row_constraints (Btor *btor, BtorExp *matrix)
{
  int i;
  BtorExp *result, *temp, *constraint;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    constraint = generate_row_constraint (btor, matrix, i);
    temp       = btor_and_exp (btor, result, constraint);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, constraint);
  }
  return result;
}

int
main ()
{
  int i;
  int error;
  int cur;
  Btor *btor;
  BtorExp *matrix, *temp, *constraint;

  /* init stuff */
  error   = 0;
  btor    = btor_new_btor ();
  indices = (BtorExp **) malloc (sizeof (BtorExp *) * SUDOKU_NUM_FIELDS);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
    indices[i] = btor_unsigned_to_exp (btor, i, SUDOKU_NUM_BITS_INDEX);
  values = (BtorExp **) malloc (sizeof (BtorExp *) * 10);
  for (i = 0; i <= 9; i++)
    values[i] = btor_unsigned_to_exp (btor, i, SUDOKU_NUM_BITS_VAL);
  matrix = btor_array_exp (btor, SUDOKU_NUM_BITS_VAL, SUDOKU_NUM_BITS_INDEX);

  /* read initial sudoku file */
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
  {
    /* skip whitespace */
    do
    {
      cur = getchar ();
      if (cur == EOF || (cur != 'x' && cur <= '0' && cur > '9'))
      {
        printf ("Input error");
        error = 1;
        goto BTOR_SUDOKU_CLEANUP;
      }

    } while (isspace (cur));
    assert (cur == 'x' || (cur > '0' && cur <= '9'));
    if (cur != 'x')
    {
      temp = btor_write_exp (btor, matrix, indices[i], values[cur - 48]);
      btor_release_exp (btor, matrix);
      matrix = temp;
    }
  }

  /* add sudoku constraints */

  /* add row constraints */
  constraint = generate_row_constraints (btor, matrix);
  btor_add_constraint_exp (btor, constraint);
  btor_release_exp (btor, constraint);

  /* clean up */
BTOR_SUDOKU_CLEANUP:
  for (i = 0; i <= SUDOKU_SIZE; i++) btor_release_exp (btor, values[i]);
  free (values);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++) btor_release_exp (btor, indices[i]);
  free (indices);
  btor_release_exp (btor, matrix);
  btor_delete_btor (btor);
  if (error) return EXIT_FAILURE;
  return EXIT_SUCCESS;
}

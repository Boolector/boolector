#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

#define SUDOKU_NUM_BITS_INDEX 7
#define SUDOKU_NUM_BITS_VAL 4
#define SUDOKU_SIZE 9
#define SUDOKU_SIZE_SQRT 3
#define SUDOKU_NUM_FIELDS (SUDOKU_SIZE * SUDOKU_SIZE)

BtorExp **indices, **values, **vars;

static BtorExp *
generate_value_constraints (Btor *btor, BtorExp *matrix)
{
  int i;
  BtorExp *lte, *gt, *and, *result, *cur, *temp;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
  {
    cur  = btor_read_exp (btor, matrix, indices[i]);
    gt   = btor_ugt_exp (btor, cur, values[0]);
    lte  = btor_ulte_exp (btor, cur, values[9]);
    and  = btor_and_exp (btor, lte, gt);
    temp = btor_and_exp (btor, result, and);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, cur);
    btor_release_exp (btor, gt);
    btor_release_exp (btor, lte);
    btor_release_exp (btor, and);
  }
  return result;
}

static BtorExp *
generate_row_constraint (Btor *btor, BtorExp *matrix, int line)
{
  int i, j;
  BtorExp *result, *temp, *read1, *read2, *ne;
  assert (btor != NULL);
  assert (matrix != NULL);
  assert (line >= 0);
  assert (line < SUDOKU_SIZE);
  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    read1 = btor_read_exp (btor, matrix, indices[line * SUDOKU_SIZE + i]);
    for (j = i + 1; j < SUDOKU_SIZE; j++)
    {
      read2 = btor_read_exp (btor, matrix, indices[line * SUDOKU_SIZE + j]);
      ne    = btor_ne_exp (btor, read1, read2);
      temp  = btor_and_exp (btor, result, ne);
      btor_release_exp (btor, result);
      result = temp;
      btor_release_exp (btor, ne);
      btor_release_exp (btor, read2);
    }
    btor_release_exp (btor, read1);
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

static BtorExp *
generate_col_constraint (Btor *btor, BtorExp *matrix, int col)
{
  int i, j;
  BtorExp *result, *temp, *read1, *read2, *ne;
  assert (btor != NULL);
  assert (matrix != NULL);
  assert (col >= 0);
  assert (col < SUDOKU_SIZE);
  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    read1 = btor_read_exp (btor, matrix, indices[i * SUDOKU_SIZE + col]);
    for (j = i + 1; j < SUDOKU_SIZE; j++)
    {
      read2 = btor_read_exp (btor, matrix, indices[j * SUDOKU_SIZE + col]);
      ne    = btor_ne_exp (btor, read1, read2);
      temp  = btor_and_exp (btor, result, ne);
      btor_release_exp (btor, result);
      result = temp;
      btor_release_exp (btor, ne);
      btor_release_exp (btor, read2);
    }
    btor_release_exp (btor, read1);
  }
  return result;
}

static BtorExp *
generate_col_constraints (Btor *btor, BtorExp *matrix)
{
  int i;
  BtorExp *result, *temp, *constraint;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    constraint = generate_col_constraint (btor, matrix, i);
    temp       = btor_and_exp (btor, result, constraint);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, constraint);
  }
  return result;
}

static BtorExp *
generate_square_constraint (Btor *btor, BtorExp *matrix, int line, int col)
{
  int i, j, x, y, counter;
  int pos[SUDOKU_SIZE];
  BtorExp *result, *temp, *read1, *read2, *ne;
  assert (btor != NULL);
  assert (matrix != NULL);
  assert (line == 0 || line == 3 || line == 6);
  assert (col == 0 || col == 3 || col == 6);

  /* compute positions in matrix */
  x       = line;
  y       = col;
  counter = 0;
  for (i = 0; i < SUDOKU_SIZE_SQRT; i++)
  {
    for (j = 0; j < SUDOKU_SIZE_SQRT; j++)
    {
      pos[counter++] = x * SUDOKU_SIZE + y;
      y++;
    }
    x++;
    y = col;
  }
  assert (counter == SUDOKU_SIZE);

  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    read1 = btor_read_exp (btor, matrix, indices[pos[i]]);
    for (j = 1; j <= SUDOKU_SIZE; j++)
    {
      read2 = btor_read_exp (btor, matrix, indices[pos[j]]);
      ne    = btor_ne_exp (btor, read1, read2);
      temp  = btor_and_exp (btor, result, ne);
      btor_release_exp (btor, result);
      result = temp;
      btor_release_exp (btor, ne);
      btor_release_exp (btor, read2);
    }
    btor_release_exp (btor, read1);
  }
  return result;
}

static BtorExp *
generate_square_constraints (Btor *btor, BtorExp *matrix)
{
  int i, j;
  BtorExp *result, *temp, *constraint;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_SIZE; i += SUDOKU_SIZE_SQRT)
  {
    for (j = 0; j < SUDOKU_SIZE; j += SUDOKU_SIZE_SQRT)
    {
      constraint = generate_square_constraint (btor, matrix, i, j);
      temp       = btor_and_exp (btor, result, constraint);
      btor_release_exp (btor, result);
      result = temp;
      btor_release_exp (btor, constraint);
    }
  }
  return result;
}

static BtorExp *
generate_var_read_relations (Btor *btor, BtorExp *matrix)
{
  int i;
  BtorExp *cur, *eq, *result, *temp;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = btor_true_exp (btor);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
  {
    cur  = btor_read_exp (btor, matrix, indices[i]);
    eq   = btor_eq_exp (btor, cur, vars[i]);
    temp = btor_and_exp (btor, result, eq);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, cur);
    btor_release_exp (btor, eq);
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

  error = 0;

  btor = btor_new_btor ();
  /* no substitution */
  btor_set_rewrite_level_btor (btor, 1);

  indices = (BtorExp **) malloc (sizeof (BtorExp *) * SUDOKU_NUM_FIELDS);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
    indices[i] = btor_unsigned_to_exp (btor, i, SUDOKU_NUM_BITS_INDEX);

  values = (BtorExp **) malloc (sizeof (BtorExp *) * 10);
  for (i = 0; i <= 9; i++)
    values[i] = btor_unsigned_to_exp (btor, i, SUDOKU_NUM_BITS_VAL);

  vars = (BtorExp **) malloc (sizeof (BtorExp *) * SUDOKU_NUM_FIELDS);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
    vars[i] = btor_var_exp (btor, SUDOKU_NUM_BITS_VAL, "var");

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

  /* add value constraints */
  constraint = generate_value_constraints (btor, matrix);
  btor_add_constraint_exp (btor, constraint);
  btor_release_exp (btor, constraint);

  /* add row constraints */
  constraint = generate_row_constraints (btor, matrix);
  btor_add_constraint_exp (btor, constraint);
  btor_release_exp (btor, constraint);

  /* add col constraints */
  constraint = generate_col_constraints (btor, matrix);
  btor_add_constraint_exp (btor, constraint);
  btor_release_exp (btor, constraint);

  /* add square constraints */
  constraint = generate_square_constraints (btor, matrix);
  btor_add_constraint_exp (btor, constraint);
  btor_release_exp (btor, constraint);

  /* add relational encoding of variables */
  constraint = generate_var_read_relations (btor, matrix);
  btor_add_constraint_exp (btor, constraint);
  btor_release_exp (btor, constraint);

  /* clean up */
BTOR_SUDOKU_CLEANUP:
  for (i = 0; i <= SUDOKU_SIZE; i++) btor_release_exp (btor, values[i]);
  free (values);

  for (i = 0; i < SUDOKU_NUM_FIELDS; i++) btor_release_exp (btor, indices[i]);
  free (indices);

  for (i = 0; i < SUDOKU_NUM_FIELDS; i++) btor_release_exp (btor, vars[i]);
  free (vars);

  btor_release_exp (btor, matrix);
  btor_delete_btor (btor);
  if (error) return EXIT_FAILURE;
  return EXIT_SUCCESS;
}

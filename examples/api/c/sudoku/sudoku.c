#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "boolector.h"
#include "btorbv.h"
#include "btorexp.h"
#include "btoropt.h"
#include "utils/btormem.h"

#define SUDOKU_NUM_BITS_INDEX 7
#define SUDOKU_NUM_BITS_VAL 4
#define SUDOKU_SIZE 9
#define SUDOKU_SIZE_SQRT 3
#define SUDOKU_NUM_FIELDS (SUDOKU_SIZE * SUDOKU_SIZE)

BoolectorNode **indices, **values, **vars;

static BoolectorNode *
generate_value_constraints (Btor *btor, BoolectorNode *matrix)
{
  int i;
  BoolectorNode *lte, *gt, *and, *result, *cur, *temp;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = boolector_true (btor);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
  {
    cur  = boolector_read (btor, matrix, indices[i]);
    gt   = boolector_ugt (btor, cur, values[0]);
    lte  = boolector_ulte (btor, cur, values[9]);
    and  = boolector_and (btor, lte, gt);
    temp = boolector_and (btor, result, and);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, cur);
    boolector_release (btor, gt);
    boolector_release (btor, lte);
    boolector_release (btor, and);
  }
  return result;
}

static BoolectorNode *
generate_row_constraint (Btor *btor, BoolectorNode *matrix, int line)
{
  int i, j;
  BoolectorNode *result, *temp, *read1, *read2, *ne;
  assert (btor != NULL);
  assert (matrix != NULL);
  assert (line >= 0);
  assert (line < SUDOKU_SIZE);
  result = boolector_true (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    read1 = boolector_read (btor, matrix, indices[line * SUDOKU_SIZE + i]);
    for (j = i + 1; j < SUDOKU_SIZE; j++)
    {
      read2 = boolector_read (btor, matrix, indices[line * SUDOKU_SIZE + j]);
      ne    = boolector_ne (btor, read1, read2);
      temp  = boolector_and (btor, result, ne);
      boolector_release (btor, result);
      result = temp;
      boolector_release (btor, ne);
      boolector_release (btor, read2);
    }
    boolector_release (btor, read1);
  }
  return result;
}

static BoolectorNode *
generate_row_constraints (Btor *btor, BoolectorNode *matrix)
{
  int i;
  BoolectorNode *result, *temp, *constraint;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = boolector_true (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    constraint = generate_row_constraint (btor, matrix, i);
    temp       = boolector_and (btor, result, constraint);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, constraint);
  }
  return result;
}

static BoolectorNode *
generate_col_constraint (Btor *btor, BoolectorNode *matrix, int col)
{
  int i, j;
  BoolectorNode *result, *temp, *read1, *read2, *ne;
  assert (btor != NULL);
  assert (matrix != NULL);
  assert (col >= 0);
  assert (col < SUDOKU_SIZE);
  result = boolector_true (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    read1 = boolector_read (btor, matrix, indices[i * SUDOKU_SIZE + col]);
    for (j = i + 1; j < SUDOKU_SIZE; j++)
    {
      read2 = boolector_read (btor, matrix, indices[j * SUDOKU_SIZE + col]);
      ne    = boolector_ne (btor, read1, read2);
      temp  = boolector_and (btor, result, ne);
      boolector_release (btor, result);
      result = temp;
      boolector_release (btor, ne);
      boolector_release (btor, read2);
    }
    boolector_release (btor, read1);
  }
  return result;
}

static BoolectorNode *
generate_col_constraints (Btor *btor, BoolectorNode *matrix)
{
  int i;
  BoolectorNode *result, *temp, *constraint;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = boolector_true (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    constraint = generate_col_constraint (btor, matrix, i);
    temp       = boolector_and (btor, result, constraint);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, constraint);
  }
  return result;
}

static BoolectorNode *
generate_square_constraint (Btor *btor,
                            BoolectorNode *matrix,
                            int line,
                            int col)
{
  int i, j, x, y, counter;
  int pos[SUDOKU_SIZE];
  BoolectorNode *result, *temp, *read1, *read2, *ne;
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

  result = boolector_true (btor);
  for (i = 0; i < SUDOKU_SIZE; i++)
  {
    read1 = boolector_read (btor, matrix, indices[pos[i]]);
    for (j = i + 1; j < SUDOKU_SIZE; j++)
    {
      read2 = boolector_read (btor, matrix, indices[pos[j]]);
      ne    = boolector_ne (btor, read1, read2);
      temp  = boolector_and (btor, result, ne);
      boolector_release (btor, result);
      result = temp;
      boolector_release (btor, ne);
      boolector_release (btor, read2);
    }
    boolector_release (btor, read1);
  }
  return result;
}

static BoolectorNode *
generate_square_constraints (Btor *btor, BoolectorNode *matrix)
{
  int i, j;
  BoolectorNode *result, *temp, *constraint;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = boolector_true (btor);
  for (i = 0; i < SUDOKU_SIZE; i += SUDOKU_SIZE_SQRT)
  {
    for (j = 0; j < SUDOKU_SIZE; j += SUDOKU_SIZE_SQRT)
    {
      constraint = generate_square_constraint (btor, matrix, i, j);
      temp       = boolector_and (btor, result, constraint);
      boolector_release (btor, result);
      result = temp;
      boolector_release (btor, constraint);
    }
  }
  return result;
}

static BoolectorNode *
generate_var_read_relations (Btor *btor, BoolectorNode *matrix)
{
  int i;
  BoolectorNode *cur, *eq, *result, *temp;
  assert (btor != NULL);
  assert (matrix != NULL);
  result = boolector_true (btor);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
  {
    cur  = boolector_read (btor, matrix, indices[i]);
    eq   = boolector_eq (btor, cur, vars[i]);
    temp = boolector_and (btor, result, eq);
    boolector_release (btor, result);
    result = temp;
    boolector_release (btor, cur);
    boolector_release (btor, eq);
  }
  return result;
}

int
main (int argc, char **argv)
{
  int i, error, cur, sat_result, counter, line_counter, dump_formula;
  char varname[6];
  const char *assignment, *assignment_dec;
  Btor *btor;
  BtorMemMgr *mm;
  BoolectorNode *matrix, *temp, *formula = 0, *constraint;
  BoolectorSort isort, esort, asort;
  BtorBitVector *bv;

  if ((argc != 2 && argc != 1)
      || (argc == 2 && strcmp (argv[1], "--dump-formula") != 0))
  {
    printf ("Usage: ./sudoku [--dump-formula]\n");
    return EXIT_SUCCESS;
  }

  if (argc == 1)
    dump_formula = 0;
  else
  {
    assert (argc == 2);
    dump_formula = 1;
  }

  /* init stuff */
  error = 0;

  btor = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_MODEL_GEN, 1);
  mm    = btor_mem_mgr_new ();
  isort = boolector_bitvec_sort (btor, SUDOKU_NUM_BITS_INDEX);
  esort = boolector_bitvec_sort (btor, SUDOKU_NUM_BITS_VAL);
  asort = boolector_array_sort (btor, isort, esort);

  if (dump_formula) boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);

  indices =
      (BoolectorNode **) malloc (sizeof (BoolectorNode *) * SUDOKU_NUM_FIELDS);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
    indices[i] = boolector_unsigned_int (btor, i, isort);

  values = (BoolectorNode **) malloc (sizeof (BoolectorNode *) * 10);
  for (i = 0; i <= 9; i++) values[i] = boolector_unsigned_int (btor, i, esort);

  vars =
      (BoolectorNode **) malloc (sizeof (BoolectorNode *) * SUDOKU_NUM_FIELDS);
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
  {
    sprintf (varname, "var%d", i);
    vars[i] = boolector_var (btor, esort, varname);
  }

  matrix = boolector_array (btor, asort, "matrix");

  /* read sudoku file */
  for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
  {
    /* skip whitespace */
    do
    {
      cur = getchar ();
      if (cur == EOF || (cur != 'x' && cur <= '0' && cur > '9'))
      {
        printf ("Input error\n");
        error = 1;
        goto BTOR_SUDOKU_CLEANUP;
      }

    } while (isspace (cur));
    assert (cur == 'x' || (cur > '0' && cur <= '9'));
    if (cur != 'x')
    {
      temp = boolector_write (btor, matrix, indices[i], values[cur - 48]);
      boolector_release (btor, matrix);
      matrix = temp;
    }
  }

  /* generate sudoku formula */

  /* generate value constraints */
  formula = generate_value_constraints (btor, matrix);

  /* add row constraints */
  constraint = generate_row_constraints (btor, matrix);
  temp       = boolector_and (btor, formula, constraint);
  boolector_release (btor, formula);
  formula = temp;
  boolector_release (btor, constraint);

  /* generate col constraints */
  constraint = generate_col_constraints (btor, matrix);
  temp       = boolector_and (btor, formula, constraint);
  boolector_release (btor, formula);
  formula = temp;
  boolector_release (btor, constraint);

  /* generate square constraints */
  constraint = generate_square_constraints (btor, matrix);
  temp       = boolector_and (btor, formula, constraint);
  boolector_release (btor, formula);
  formula = temp;
  boolector_release (btor, constraint);

  /* generate relational encoding of variables */
  constraint = generate_var_read_relations (btor, matrix);
  temp       = boolector_and (btor, formula, constraint);
  boolector_release (btor, formula);
  formula = temp;
  boolector_release (btor, constraint);

  if (dump_formula)
    boolector_dump_btor_node (btor, stdout, formula);
  else
  {
    /* add formula */
    boolector_assert (btor, formula);

    sat_result = boolector_sat (btor);
    if (sat_result == BOOLECTOR_UNSAT)
      printf ("Sudoku instance is not solvable\n");
    else
    {
      assert (sat_result == BOOLECTOR_SAT);
      counter      = 0;
      line_counter = 0;
      for (i = 0; i < SUDOKU_NUM_FIELDS; i++)
      {
        assignment     = boolector_bv_assignment (btor, vars[i]);
        bv             = btor_bv_char_to_bv (mm, assignment);
        assignment_dec = btor_bv_to_dec_char (mm, bv);
        btor_bv_free (mm, bv);
        printf ("%s", assignment_dec);
        counter++;
        if (counter % SUDOKU_SIZE_SQRT == 0) printf (" ");
        if (counter == SUDOKU_SIZE)
        {
          printf ("\n");
          counter = 0;
          line_counter++;
        }
        if (line_counter == SUDOKU_SIZE_SQRT)
        {
          printf ("\n");
          line_counter = 0;
        }
        btor_mem_freestr (mm, (char *) assignment_dec);
        boolector_free_bv_assignment (btor, assignment);
      }
    }
  }

  /* clean up */
BTOR_SUDOKU_CLEANUP:
  for (i = 0; i <= SUDOKU_SIZE; i++) boolector_release (btor, values[i]);
  free (values);

  for (i = 0; i < SUDOKU_NUM_FIELDS; i++) boolector_release (btor, indices[i]);
  free (indices);

  for (i = 0; i < SUDOKU_NUM_FIELDS; i++) boolector_release (btor, vars[i]);
  free (vars);

  boolector_release (btor, formula);
  boolector_release (btor, matrix);
  boolector_release_sort (btor, isort);
  boolector_release_sort (btor, esort);
  boolector_release_sort (btor, asort);
  boolector_delete (btor);
  btor_mem_mgr_delete (mm);
  if (error) return EXIT_FAILURE;
  return EXIT_SUCCESS;
}

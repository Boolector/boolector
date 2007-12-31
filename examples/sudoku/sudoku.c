#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

#define BTOR_SUDOKU_NUM_BITS_INDEX 7
#define BTOR_SUDOKU_NUM_BITS_ELEM 4
#define BTOR_SUDOKU_NUM_FIELDS 81

int
main (int argc, char **argv)
{
  int i;
  int error;
  int cur;
  Btor *btor;
  BtorExp **indices, **elements, *matrix, *temp;

  /* init stuff */
  error   = 0;
  btor    = btor_new_btor ();
  indices = (BtorExp **) malloc (sizeof (BtorExp *) * BTOR_SUDOKU_NUM_FIELDS);
  for (i = 0; i < BTOR_SUDOKU_NUM_FIELDS; i++)
    indices[i] = btor_unsigned_to_exp (btor, i, BTOR_SUDOKU_NUM_BITS_INDEX);
  elements = (BtorExp **) malloc (sizeof (BtorExp *) * 10);
  for (i = 1; i <= 9; i++)
    elements[i] = btor_unsigned_to_exp (btor, i, BTOR_SUDOKU_NUM_BITS_ELEM);
  matrix = btor_array_exp (
      btor, BTOR_SUDOKU_NUM_BITS_ELEM, BTOR_SUDOKU_NUM_BITS_INDEX);

  /* read initial sudoku file */
  for (i = 0; i < BTOR_SUDOKU_NUM_FIELDS; i++)
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
      temp = btor_write_exp (btor, matrix, indices[i], elements[cur - 48]);
      btor_release_exp (btor, matrix);
      matrix = temp;
    }
  }

  /* clean up */
BTOR_SUDOKU_CLEANUP:
  for (i = 1; i <= 9; i++) btor_release_exp (btor, elements[i]);
  free (elements);
  for (i = 0; i < BTOR_SUDOKU_NUM_FIELDS; i++)
    btor_release_exp (btor, indices[i]);
  free (indices);
  btor_release_exp (btor, matrix);
  btor_delete_btor (btor);
  if (error) return EXIT_FAILURE;
  return EXIT_SUCCESS;
}

/*
The BtorFMT software provides a generic parser for the BTOR format.
In contrast to Boolector it falls under the following MIT style license:

Copyright (c) 2012-2018, Armin Biere, Johannes Kepler University, Linz
Copyright (c) 2017, Mathias Preiner
Copyright (c) 2017, Aina Niemetz

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.
*/

#ifndef btorfmt_h_INCLUDED
#define btorfmt_h_INCLUDED

/*------------------------------------------------------------------------*/
/* The BTOR format is described in our BPR'08 paper and beside comment lines
 * starting with ';', as well empty lines, consists of the following lines:
 *
 *  <id> <tag> <len> [ <idxlen> ] [ <sid> ... ] [ <const> | <sym> ]
 *
 * Arguments are seperated by a singled space character and no additional
 * spaces are allowed at the end-of-the line before the new line character.
 * The <id> is a unique postive id, the output length is <len>, and <tag>
 * is decribed below.  For arrays and functions <idxlen> is specified too.
 * If the line describes an operator, signed but non zero ids are used do
 * reference arguments.  For constants <const> is a string representing
 * a binary, decimal or hexadecimal constant.  Finally for basic variables,
 * arrays, states, functions <sym> is an optional symbol name.
 */
/*------------------------------------------------------------------------*/

#include <stdio.h>

/*------------------------------------------------------------------------*/

#define BTOR_FORMAT_MAXID (1l << 40) /* assume 64-bit compilation */
#define BTOR_FORMAT_MAXBITWIDTH ((1l << 31) - 1)

/*------------------------------------------------------------------------*/

typedef struct BtorFormatReader BtorFormatReader;
typedef struct BtorFormatLine BtorFormatLine;
typedef struct BtorFormatSort BtorFormatSort;
typedef struct BtorFormatLineIterator BtorFormatLineIterator;
typedef enum BtorFormatTag BtorFormatTag;
typedef enum BtorFormatSortTag BtorFormatSortTag;

/*------------------------------------------------------------------------*/
/* These BTOR format tags can be used for fast(er) traversal and operations
 * on BTOR format lines for instance in a switch statement in client code.
 * Alternatively client code can use the name of the BTOR format tag, which
 * is a C string also (redundantly) contained in the format line. This needs
 * string comparisons and thus is slower even if client code would use an
 * additional hash table.
 */
enum BtorFormatTag
{
  BTOR_FORMAT_TAG_add,
  BTOR_FORMAT_TAG_and,
  BTOR_FORMAT_TAG_bad,
  BTOR_FORMAT_TAG_concat,
  BTOR_FORMAT_TAG_const,
  BTOR_FORMAT_TAG_constraint,
  BTOR_FORMAT_TAG_constd,
  BTOR_FORMAT_TAG_consth,
  BTOR_FORMAT_TAG_dec,
  BTOR_FORMAT_TAG_eq,
  BTOR_FORMAT_TAG_fair,
  BTOR_FORMAT_TAG_iff,
  BTOR_FORMAT_TAG_implies,
  BTOR_FORMAT_TAG_inc,
  BTOR_FORMAT_TAG_init,
  BTOR_FORMAT_TAG_input,
  BTOR_FORMAT_TAG_ite,
  BTOR_FORMAT_TAG_justice,
  BTOR_FORMAT_TAG_mul,
  BTOR_FORMAT_TAG_nand,
  BTOR_FORMAT_TAG_ne,
  BTOR_FORMAT_TAG_neg,
  BTOR_FORMAT_TAG_next,
  BTOR_FORMAT_TAG_nor,
  BTOR_FORMAT_TAG_not,
  BTOR_FORMAT_TAG_one,
  BTOR_FORMAT_TAG_ones,
  BTOR_FORMAT_TAG_or,
  BTOR_FORMAT_TAG_output,
  BTOR_FORMAT_TAG_read,
  BTOR_FORMAT_TAG_redand,
  BTOR_FORMAT_TAG_redor,
  BTOR_FORMAT_TAG_redxor,
  BTOR_FORMAT_TAG_rol,
  BTOR_FORMAT_TAG_ror,
  BTOR_FORMAT_TAG_saddo,
  BTOR_FORMAT_TAG_sdiv,
  BTOR_FORMAT_TAG_sdivo,
  BTOR_FORMAT_TAG_sext,
  BTOR_FORMAT_TAG_sgt,
  BTOR_FORMAT_TAG_sgte,
  BTOR_FORMAT_TAG_slice,
  BTOR_FORMAT_TAG_sll,
  BTOR_FORMAT_TAG_slt,
  BTOR_FORMAT_TAG_slte,
  BTOR_FORMAT_TAG_sort,
  BTOR_FORMAT_TAG_smod,
  BTOR_FORMAT_TAG_smulo,
  BTOR_FORMAT_TAG_sra,
  BTOR_FORMAT_TAG_srem,
  BTOR_FORMAT_TAG_srl,
  BTOR_FORMAT_TAG_ssubo,
  BTOR_FORMAT_TAG_state,
  BTOR_FORMAT_TAG_sub,
  BTOR_FORMAT_TAG_uaddo,
  BTOR_FORMAT_TAG_udiv,
  BTOR_FORMAT_TAG_uext,
  BTOR_FORMAT_TAG_ugt,
  BTOR_FORMAT_TAG_ugte,
  BTOR_FORMAT_TAG_ult,
  BTOR_FORMAT_TAG_ulte,
  BTOR_FORMAT_TAG_umulo,
  BTOR_FORMAT_TAG_urem,
  BTOR_FORMAT_TAG_usubo,
  BTOR_FORMAT_TAG_write,
  BTOR_FORMAT_TAG_xnor,
  BTOR_FORMAT_TAG_xor,
  BTOR_FORMAT_TAG_zero,
};

enum BtorFormatSortTag
{
  BTOR_FORMAT_TAG_SORT_array,
  BTOR_FORMAT_TAG_SORT_bitvec,
};

/*------------------------------------------------------------------------*/

struct BtorFormatSort
{
  long id;
  BtorFormatSortTag tag;
  const char *name;
  union
  {
    struct
    {
      long index;
      long element;
    } array;
    struct
    {
      unsigned width;
    } bitvec;
  };
};

struct BtorFormatLine
{
  long id;           /* positive id (non zero)                 */
  long lineno;       /* line number in original file           */
  const char *name;  /* name in ASCII: "and", "add", ...       */
  BtorFormatTag tag; /* same as name but encoded as integer    */
  BtorFormatSort sort;
  long init, next; /* non zero if initialized or has next    */
  char *constant;  /* non zero for const, constd, consth     */
  char *symbol;    /* optional for: var array state input    */
  unsigned nargs;  /* number of arguments                    */
  long *args;      /* non zero ids up to nargs               */
};

struct BtorFormatLineIterator
{
  BtorFormatReader *reader;
  long next;
};

/*------------------------------------------------------------------------*/
/* Constructor, setting options and destructor:
 */
BtorFormatReader *btorfmt_new ();
void btorfmt_delete (BtorFormatReader *);

/*------------------------------------------------------------------------*/
/* The 'btorfmt_read_lines' function returns zero on failure.  In this
 * case you can call 'btorfmt_error' to obtain a description of
 * the actual read or parse error, which includes the line number where
 * the error occurred.
 */
int btorfmt_read_lines (BtorFormatReader *, FILE *);
const char *btorfmt_error (BtorFormatReader *);

/*------------------------------------------------------------------------*/
/* Iterate over all read format lines:
 *
 *   BtorFormatLineIterator it = btorfmt_iter_init (bfr);
 *   BtorFormatLine * l;
 *   while ((l = btorfmt_iter_next (&it)))
 *     do_something_with_btor_format_line (l);
 */
BtorFormatLineIterator btorfmt_iter_init (BtorFormatReader *bfr);
BtorFormatLine *btorfmt_iter_next (BtorFormatLineIterator *);

/*------------------------------------------------------------------------*/
/* The reader maintains a mapping of ids to format lines.  This mapping
 * can be retrieved with the following function.  Note, however, that
 * ids might be negative and denote the negation of the actual node.
 */
long btorfmt_max_id (BtorFormatReader *);
BtorFormatLine *btorfmt_get_line_by_id (BtorFormatReader *, long id);

/*------------------------------------------------------------------------*/

#endif

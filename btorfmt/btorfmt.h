/*
The BtorFMT software provides a generic parser for the BTOR format.
In contrast to Boolector it falls under the following MIT style license:

Copyright (c) 2012-2015, Armin Biere, Johannes Kepler University, Linz

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

#include <stdio.h>

/*------------------------------------------------------------------------*/

#define BTOR_FORMAT_MAXID (1l << 40) /* assume 64-bit compilation */
#define BTOR_FORMAT_MAXLEN ((1l << 31) - 1)

/*------------------------------------------------------------------------*/

typedef struct BtorFormatReader BtorFormatReader;
typedef struct BtorFormatLine BtorFormatLine;
typedef struct BtorFormatType BtorFormatType;
typedef struct BtorFormatLineIterator BtorFormatLineIterator;

/*------------------------------------------------------------------------*/
/*
 * These BTOR format tags can be used for fast(er) traversal and operations
 * on BTOR format lines for instance in a switch statement in client code.
 * Alternatively client code can use the name of the BTOR format tag, which
 * is a C string also (redundantly) contained in the format line. This needs
 * string comparisons and thus is slower even if client code would use an
 * additional hash table.
 */
typedef enum BtorFormatTag
{
  BTOR_FORMAT_TAG_add,
  BTOR_FORMAT_TAG_and,
  BTOR_FORMAT_TAG_array,
  BTOR_FORMAT_TAG_concat,
  BTOR_FORMAT_TAG_cond,
  BTOR_FORMAT_TAG_acond,
  BTOR_FORMAT_TAG_const,
  BTOR_FORMAT_TAG_constd,
  BTOR_FORMAT_TAG_consth,
  BTOR_FORMAT_TAG_eq,
  BTOR_FORMAT_TAG_iff,
  BTOR_FORMAT_TAG_implies,
  BTOR_FORMAT_TAG_mul,
  BTOR_FORMAT_TAG_nand,
  BTOR_FORMAT_TAG_neg,
  BTOR_FORMAT_TAG_inc,
  BTOR_FORMAT_TAG_dec,
  BTOR_FORMAT_TAG_ne,
  BTOR_FORMAT_TAG_next,
  BTOR_FORMAT_TAG_anext,
  BTOR_FORMAT_TAG_nor,
  BTOR_FORMAT_TAG_not,
  BTOR_FORMAT_TAG_one,
  BTOR_FORMAT_TAG_ones,
  BTOR_FORMAT_TAG_or,
  BTOR_FORMAT_TAG_proxy,
  BTOR_FORMAT_TAG_read,
  BTOR_FORMAT_TAG_redand,
  BTOR_FORMAT_TAG_redor,
  BTOR_FORMAT_TAG_redxor,
  BTOR_FORMAT_TAG_rol,
  BTOR_FORMAT_TAG_root,
  BTOR_FORMAT_TAG_ror,
  BTOR_FORMAT_TAG_saddo,
  BTOR_FORMAT_TAG_sdivo,
  BTOR_FORMAT_TAG_sdiv,
  BTOR_FORMAT_TAG_sext,
  BTOR_FORMAT_TAG_sgte,
  BTOR_FORMAT_TAG_sgt,
  BTOR_FORMAT_TAG_slice,
  BTOR_FORMAT_TAG_sll,
  BTOR_FORMAT_TAG_slte,
  BTOR_FORMAT_TAG_slt,
  BTOR_FORMAT_TAG_smod,
  BTOR_FORMAT_TAG_smulo,
  BTOR_FORMAT_TAG_sra,
  BTOR_FORMAT_TAG_srem,
  BTOR_FORMAT_TAG_srl,
  BTOR_FORMAT_TAG_ssubo,
  BTOR_FORMAT_TAG_sub,
  BTOR_FORMAT_TAG_uaddo,
  BTOR_FORMAT_TAG_udiv,
  BTOR_FORMAT_TAG_uext,
  BTOR_FORMAT_TAG_ugte,
  BTOR_FORMAT_TAG_ugt,
  BTOR_FORMAT_TAG_ulte,
  BTOR_FORMAT_TAG_ult,
  BTOR_FORMAT_TAG_umulo,
  BTOR_FORMAT_TAG_urem,
  BTOR_FORMAT_TAG_usubo,
  BTOR_FORMAT_TAG_var,
  BTOR_FORMAT_TAG_write,
  BTOR_FORMAT_TAG_xnor,
  BTOR_FORMAT_TAG_xor,
  BTOR_FORMAT_TAG_zero,
} BtorFormatTag;

/*------------------------------------------------------------------------*/

struct BtorFormatType
{
  int len;     // length = bit-width
  int idxlen;  // index length
               // non-zero for arrays and functions
};

struct BtorFormatLine
{
  long id;              // positive id (non zero)
  const char *name;     // name in ASCCII: "and", "add", ...
  BtorFormatTag tag;    // same as name but encoded as integer
  BtorFormatType type;  // length = bit-width (also for indices)
  int arity;            // redundant but useful (0 <= arity <= 3)
  long arg[3];          // non zero ids up to arity
  char *constant;       // non zero for const, constd, consth
  char *symbol;         // optional for: var, array, latch, input
  void *data;           // user data
};

struct BtorFormatLineIterator
{
  BtorFormatReader *reader;
  long next;
};

/*------------------------------------------------------------------------*/
/*
 * Constructor, setting options and destructor:
 */
BtorFormatReader *new_btor_format_reader ();
void set_btor_format_reader_verbosity (BtorFormatReader *, int verbosity);
void set_btor_format_reader_prefix (BtorFormatReader *, const char *prefix);
void delete_btor_format_reader (BtorFormatReader *);

/*------------------------------------------------------------------------*/
/*
 * The 'read_btor_format_lines' function returns zero on failure.  In this
 * case you can call 'error_btor_format_reader' to obtain a description of
 * the actual read or parse error, which includes the line number where
 * the error occurred.
 */
int read_btor_format_lines (BtorFormatReader *, FILE *);
const char *error_btor_format_reader (BtorFormatReader *);

/*------------------------------------------------------------------------*/
/*
 * Iterate over all read format lines:
 *
 *   BtorFormatLineIterator it = iterate_btor_format_line (bfr);
 *   BtorFormatLine * l;
 *   while ((l = next_btor_format_line (&it)))
 *     do_something_with_btor_format_line (l);
 */
BtorFormatLineIterator iterate_btor_format_line (BtorFormatReader *bfr);
BtorFormatLine *next_btor_format_line (BtorFormatLineIterator *);

/*------------------------------------------------------------------------*/
/*
 * The reader maintains a mapping of ids to format lines.  This mapping
 * can be retrieved with the following function.  Note, however, that
 * ids might be negative and denote the negation of the actual node.
 */
BtorFormatLine *get_btor_format_line_from_id (BtorFormatReader *, long id);

/*------------------------------------------------------------------------*/

#endif

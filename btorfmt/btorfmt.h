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

typedef struct BtorFormatReader BtorFormatReader;
typedef struct BtorFormatLine BtorFormatLine;

typedef enum BtorFormatTag
{
  BTOR_FORMAT_INVALID_TAG = 0,
  BTOR_FORMAT_TAG_ADD,
  BTOR_FORMAT_TAG_AND,
  BTOR_FORMAT_TAG_ARRAY,
  BTOR_FORMAT_TAG_CONCAT,
  BTOR_FORMAT_TAG_COND,
  BTOR_FORMAT_TAG_ACOND,
  BTOR_FORMAT_TAG_CONST,
  BTOR_FORMAT_TAG_CONSTD,
  BTOR_FORMAT_TAG_CONSTH,
  BTOR_FORMAT_TAG_EQ,
  BTOR_FORMAT_TAG_IFF,
  BTOR_FORMAT_TAG_IMPLIES,
  BTOR_FORMAT_TAG_MUL,
  BTOR_FORMAT_TAG_NAND,
  BTOR_FORMAT_TAG_NEG,
  BTOR_FORMAT_TAG_INC,
  BTOR_FORMAT_TAG_DEC,
  BTOR_FORMAT_TAG_NE,
  BTOR_FORMAT_TAG_NEXT,
  BTOR_FORMAT_TAG_ANEXT,
  BTOR_FORMAT_TAG_NOR,
  BTOR_FORMAT_TAG_NOT,
  BTOR_FORMAT_TAG_ONE,
  BTOR_FORMAT_TAG_ONES,
  BTOR_FORMAT_TAG_OR,
  BTOR_FORMAT_TAG_PROXY,
  BTOR_FORMAT_TAG_READ,
  BTOR_FORMAT_TAG_REDAND,
  BTOR_FORMAT_TAG_REDOR,
  BTOR_FORMAT_TAG_REDXOR,
  BTOR_FORMAT_TAG_ROL,
  BTOR_FORMAT_TAG_ROOT,
  BTOR_FORMAT_TAG_ROR,
  BTOR_FORMAT_TAG_SADDO,
  BTOR_FORMAT_TAG_SDIVO,
  BTOR_FORMAT_TAG_SDIV,
  BTOR_FORMAT_TAG_SEXT,
  BTOR_FORMAT_TAG_SGTE,
  BTOR_FORMAT_TAG_SGT,
  BTOR_FORMAT_TAG_SLICE,
  BTOR_FORMAT_TAG_SLL,
  BTOR_FORMAT_TAG_SLTE,
  BTOR_FORMAT_TAG_SLT,
  BTOR_FORMAT_TAG_SMOD,
  BTOR_FORMAT_TAG_SMULO,
  BTOR_FORMAT_TAG_SRA,
  BTOR_FORMAT_TAG_SREM,
  BTOR_FORMAT_TAG_SRL,
  BTOR_FORMAT_TAG_SSUBO,
  BTOR_FORMAT_TAG_SUB,
  BTOR_FORMAT_TAG_UADDO,
  BTOR_FORMAT_TAG_UDIV,
  BTOR_FORMAT_TAG_UEXT,
  BTOR_FORMAT_TAG_UGTE,
  BTOR_FORMAT_TAG_UGT,
  BTOR_FORMAT_TAG_ULTE,
  BTOR_FORMAT_TAG_ULT,
  BTOR_FORMAT_TAG_UMULO,
  BTOR_FORMAT_TAG_UREM,
  BTOR_FORMAT_TAG_USUBO,
  BTOR_FORMAT_TAG_VAR,
  BTOR_FORMAT_TAG_WRITE,
  BTOR_FORMAT_TAG_XNOR,
  BTOR_FORMAT_TAG_XOR,
  BTOR_FORMAT_TAG_ZERO,
} BtorFormatTag;

/*------------------------------------------------------------------------*/

struct BtorFormatLine
{
  int id;
  BtorFormatTag tag;
  int len, ilen;
  char *symbol;
  int arg[3];
  void *data;  // for external usage ...
};

/*------------------------------------------------------------------------*/

BtorFormatReader *new_btor_format_reader ();
void set_btor_format_reader_verbosity (BtorFormatReader *, int verbosity);
void set_btor_format_reader_prefix (BtorFormatReader *, const char *prefix);
void delete_btor_format_reader (BtorFormatReader *);

/*------------------------------------------------------------------------*/

BtorFormatLine **read_btor_format_lines (BtorFormatReader *, FILE *);
const char *error_btor_format_reader (BtorFormatReader *);

/*------------------------------------------------------------------------*/

#endif

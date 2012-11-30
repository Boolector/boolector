#ifndef btorfmt_h_INCLUDED
#define btorfmt_h_INCLUDED

/*------------------------------------------------------------------------*/

#include <stdio.h>

/*------------------------------------------------------------------------*/

typedef struct BtorFormatReader BtorFormatReader;
typedef struct BtorFormatLine BtorFormatLine;

typedef enum BtorFormatTag
{
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

#define BTOR_FORMAT_LINE_MAX_ARGS 7

struct BtorFormatLine
{
  int id;
  BtorFormatTag tag;
  char *symbol;
  int len, ilen;
  int arg[3];
};

/*------------------------------------------------------------------------*/

BtorFormatReader *new_btor_format_reader ();
void delete_btor_format_reader (BtorFormatReader *);

/*------------------------------------------------------------------------*/

BtorFormatLine **read_btor_format_lines (BtorFormatReader *, FILE *);
const char *error_btor_format_reader (BtorFormatReader *);

/*------------------------------------------------------------------------*/

#endif

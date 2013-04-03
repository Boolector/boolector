#include "btormisc.h"

char g_strbuf[256];
int g_strbufpos = 0;

char *
node2string (BtorNode *exp)
{
  const char *name;
  char strbuf[100], *bufstart;
  int len;

  if (!exp) return "0";

  exp = BTOR_REAL_ADDR_NODE (exp);

  switch (exp->kind)
  {
    case BTOR_INVALID_NODE: name = "invalid"; break;
    case BTOR_BV_CONST_NODE: name = "const"; break;
    case BTOR_BV_VAR_NODE: name = "var"; break;
    case BTOR_ARRAY_VAR_NODE: name = "array"; break;
    case BTOR_PARAM_NODE: name = "param"; break;
    case BTOR_SLICE_NODE: name = "slice"; break;
    case BTOR_AND_NODE: name = "and"; break;
    case BTOR_BEQ_NODE:
    case BTOR_AEQ_NODE: name = "eq"; break;
    case BTOR_ADD_NODE: name = "add"; break;
    case BTOR_MUL_NODE: name = "mul"; break;
    case BTOR_ULT_NODE: name = "ult"; break;
    case BTOR_SLL_NODE: name = "sll"; break;
    case BTOR_SRL_NODE: name = "srl"; break;
    case BTOR_UDIV_NODE: name = "udiv"; break;
    case BTOR_UREM_NODE: name = "urem"; break;
    case BTOR_CONCAT_NODE: name = "concat"; break;
    case BTOR_READ_NODE: name = "read"; break;
    case BTOR_LAMBDA_NODE: name = "lambda"; break;
    case BTOR_WRITE_NODE: name = "write"; break;
    case BTOR_BCOND_NODE: name = "bcond"; break;
    case BTOR_ACOND_NODE: name = "acond"; break;
    case BTOR_PROXY_NODE: name = "proxy"; break;
  }

  if (exp->kind == BTOR_SLICE_NODE)
    sprintf (strbuf,
             "%d %s %d %d %d",
             BTOR_GET_ID_NODE (exp),
             name,
             BTOR_GET_ID_NODE (exp->e[0]),
             exp->upper,
             exp->lower);
  else if (BTOR_IS_BINARY_NODE (exp))
    sprintf (strbuf,
             "%d %s %d %d",
             BTOR_GET_ID_NODE (exp),
             name,
             BTOR_GET_ID_NODE (exp->e[0]),
             BTOR_GET_ID_NODE (exp->e[1]));
  else if (BTOR_IS_TERNARY_NODE (exp))
    sprintf (strbuf,
             "%d %s %d %d %d",
             BTOR_GET_ID_NODE (exp),
             name,
             BTOR_GET_ID_NODE (exp->e[0]),
             BTOR_GET_ID_NODE (exp->e[1]),
             BTOR_GET_ID_NODE (exp->e[2]));
  else if (exp->kind == BTOR_BV_VAR_NODE || exp->kind == BTOR_PARAM_NODE)
    sprintf (strbuf, "%d %s %s", BTOR_GET_ID_NODE (exp), name, exp->symbol);
  else
    sprintf (strbuf, "%d %s", BTOR_GET_ID_NODE (exp), name);

  len = strlen (strbuf) + 1;

  if (g_strbufpos + len > 255) g_strbufpos = 0;

  bufstart = g_strbuf + g_strbufpos;
  sprintf (bufstart, "%s", strbuf);
  g_strbufpos += len;

  return bufstart;
}

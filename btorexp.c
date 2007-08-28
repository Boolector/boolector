#include "btorexp.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorconst.h"
#include "btorsat.h"
#include "btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/

struct BtorExpUniqueTable
{
  int size;
  int num_elements;
  struct BtorExp **chains;
};

typedef struct BtorExpUniqueTable BtorExpUniqueTable;

#define BTOR_INIT_EXP_UNIQUE_TABLE(mm, table)                          \
  do                                                                   \
  {                                                                    \
    assert (mm != NULL);                                               \
    (table).size         = 1;                                          \
    (table).num_elements = 0;                                          \
    (table).chains =                                                   \
        (BtorExp **) btor_calloc (mm, (size_t) 1, sizeof (BtorExp *)); \
  } while (0)

#define BTOR_RELEASE_EXP_UNIQUE_TABLE(mm, table)                       \
  do                                                                   \
  {                                                                    \
    assert (mm != NULL);                                               \
    btor_free (mm, (table).chains, sizeof (BtorExp *) * (table).size); \
  } while (0)

#define BTOR_EXP_UNIQUE_TABLE_LIMIT 30
#define BTOR_EXP_UNIQUE_TABLE_PRIME 2000000137u

struct BtorExpMgr
{
  BtorMemMgr *mm;
  BtorExpUniqueTable table;
  BtorExpPtrStack assigned_exps;
  BtorExpPtrStack vars;
  BtorExpPtrStack arrays;
  BtorAIGVecMgr *avmgr;
  int id;
  int rewrite_level;
  int dump_trace;
  int verbosity;
  BtorReadEnc read_enc;
  FILE *trace_file;
};

struct BtorReadObjSortObj
{
  BtorExpMgr *emgr;
  BtorReadObj *obj;
};

typedef struct BtorReadObjSortObj BtorReadObjSortObj;

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* Auxilliary                                                             */
/*------------------------------------------------------------------------*/

static void
print_verbose_msg (char *msg)
{
  assert (msg != NULL);
  fprintf (stderr, "[btorexp] %s", msg);
  fflush (stderr);
}

static char *
zeros_string (BtorExpMgr *emgr, int len)
{
  int i        = 0;
  char *string = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string = (char *) btor_malloc (emgr->mm, sizeof (char) * (len + 1));
  for (i = 0; i < len; i++) string[i] = '0';
  string[len] = '\0';
  return string;
}

static char *
ones_string (BtorExpMgr *emgr, int len)
{
  int i        = 0;
  char *string = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string = (char *) btor_malloc (emgr->mm, sizeof (char) * (len + 1));
  for (i = 0; i < len; i++) string[i] = '1';
  string[len] = '\0';
  return string;
}

static char *
int_to_string (BtorExpMgr *emgr, int x, int len)
{
  int i        = 0;
  char *string = NULL;
  assert (emgr != NULL);
  assert (x >= 0);
  assert (len > 0);
  string = (char *) btor_malloc (emgr->mm, sizeof (char) * (len + 1));
  for (i = len - 1; i >= 0; i--)
  {
    string[i] = x % 2 == 0 ? '0' : '1';
    x >>= 1;
  }
  string[len] = '\0';
  return string;
}

static int
is_zero_string (BtorExpMgr *emgr, const char *string, int len)
{
  int i = 0;
  assert (emgr != NULL);
  assert (string != NULL);
  assert (len > 0);
  for (i = 0; i < len; i++)
    if (string[i] != '0') return 0;
  return 1;
}

static int
is_one_string (BtorExpMgr *emgr, const char *string, int len)
{
  int i = 0;
  assert (emgr != NULL);
  assert (string != NULL);
  assert (len > 0);
  if (string[len - 1] != '1') return 0;
  for (i = 0; i < len - 1; i++)
    if (string[i] != '0') return 0;
  return 1;
}

/*------------------------------------------------------------------------*/
/* BtorReadObjSort                                                        */
/*------------------------------------------------------------------------*/

static BtorReadObjSortObj *
new_read_obj_sort_obj (BtorExpMgr *emgr, BtorReadObj *obj)
{
  BtorReadObjSortObj *result = NULL;
  assert (emgr != NULL);
  assert (obj != NULL);
  result       = btor_malloc (emgr->mm, sizeof (BtorReadObjSortObj));
  result->emgr = emgr;
  result->obj  = obj;
  return result;
}

static void
delete_read_obj_sort_obj (BtorExpMgr *emgr, BtorReadObjSortObj *sobj)
{
  assert (emgr != NULL);
  assert (sobj != NULL);
  btor_free (emgr->mm, sobj, sizeof (BtorReadObjSortObj));
}

/*------------------------------------------------------------------------*/
/* BtorReadObj                                                            */
/*------------------------------------------------------------------------*/

static BtorReadObj *
new_read_obj (BtorExpMgr *emgr, BtorExp *var, BtorExp *index)
{
  BtorReadObj *result = NULL;
  assert (emgr != NULL);
  assert (var != NULL);
  assert (index != NULL);
  result        = (BtorReadObj *) btor_malloc (emgr->mm, sizeof (BtorReadObj));
  result->var   = btor_copy_exp (emgr, var);
  result->index = btor_copy_exp (emgr, index);
  return result;
}

static void
delete_read_obj (BtorExpMgr *emgr, BtorReadObj *obj)
{
  assert (emgr != NULL);
  assert (obj != NULL);
  btor_release_exp (emgr, obj->var);
  btor_release_exp (emgr, obj->index);
  btor_free (emgr->mm, obj, sizeof (BtorReadObj));
}

static void
encode_read (BtorExpMgr *emgr,
             BtorExp *index1,
             BtorExp *index2,
             BtorExp *var1,
             BtorExp *var2)
{
  BtorMemMgr *mm        = NULL;
  BtorAIGMgr *amgr      = NULL;
  BtorSATMgr *smgr      = NULL;
  BtorAIGVec *av_index1 = NULL;
  BtorAIGVec *av_index2 = NULL;
  BtorAIGVec *av_var1   = NULL;
  BtorAIGVec *av_var2   = NULL;
  BtorAIG *aig1         = NULL;
  BtorAIG *aig2         = NULL;
  BtorIntStack diffs;
  int k            = 0;
  int len          = 0;
  int i_k          = 0;
  int j_k          = 0;
  int d_k          = 0;
  int e            = 0;
  int a_k          = 0;
  int b_k          = 0;
  int is_different = 0;
  assert (emgr != NULL);
  assert (index1 != NULL);
  assert (index2 != NULL);
  assert (var1 != NULL);
  assert (var2 != NULL);
  assert (!BTOR_IS_INVERTED_EXP (var1));
  assert (!BTOR_IS_INVERTED_EXP (var2));
  mm   = emgr->mm;
  amgr = btor_get_aig_mgr_aigvec_mgr (emgr->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  if (BTOR_IS_INVERTED_EXP (index1))
    av_index1 = btor_not_aigvec (emgr->avmgr, BTOR_REAL_ADDR_EXP (index1)->av);
  else
    av_index1 = btor_copy_aigvec (emgr->avmgr, index1->av);
  assert (av_index1 != NULL);
  if (BTOR_IS_INVERTED_EXP (index2))
    av_index2 = btor_not_aigvec (emgr->avmgr, BTOR_REAL_ADDR_EXP (index2)->av);
  else
    av_index2 = btor_copy_aigvec (emgr->avmgr, index2->av);
  assert (av_index2 != NULL);
  av_var1 = var1->av;
  assert (av_var1 != NULL);
  av_var2 = var2->av;
  assert (av_var2 != NULL);
  is_different = btor_is_different_aigvec (emgr->avmgr, av_index1, av_index2);
  if (is_different && btor_is_const_aigvec (emgr->avmgr, av_index1)
      && btor_is_const_aigvec (emgr->avmgr, av_index2))
  {
    btor_release_delete_aigvec (emgr->avmgr, av_index1);
    btor_release_delete_aigvec (emgr->avmgr, av_index2);
    return;
  }
  len = av_index1->len;
  if (is_different)
  {
    BTOR_INIT_STACK (diffs);
    for (k = 0; k < len; k++)
    {
      aig1 = av_index1->aigs[k];
      aig2 = av_index2->aigs[k];
      if (!BTOR_IS_CONST_AIG (aig1))
      {
        if (BTOR_REAL_ADDR_AIG (aig1)->cnf_id == 0)
          BTOR_REAL_ADDR_AIG (aig1)->cnf_id = btor_next_cnf_id_sat_mgr (smgr);
        if (BTOR_IS_INVERTED_AIG (aig1))
          i_k = -BTOR_REAL_ADDR_AIG (aig1)->cnf_id;
        else
          i_k = aig1->cnf_id;
        assert (i_k != 0);
      }
      if (!BTOR_IS_CONST_AIG (aig2))
      {
        if (BTOR_REAL_ADDR_AIG (aig2)->cnf_id == 0)
          BTOR_REAL_ADDR_AIG (aig2)->cnf_id = btor_next_cnf_id_sat_mgr (smgr);
        if (BTOR_IS_INVERTED_AIG (aig2))
          j_k = -BTOR_REAL_ADDR_AIG (aig2)->cnf_id;
        else
          j_k = aig2->cnf_id;
        assert (j_k != 0);
      }
      if ((((unsigned long int) aig1) ^ ((unsigned long int) aig2)) != 1ul)
      {
        d_k = btor_next_cnf_id_sat_mgr (smgr);
        assert (d_k != 0);
        BTOR_PUSH_STACK (mm, diffs, d_k);
        if (aig1 != BTOR_AIG_TRUE && aig2 != BTOR_AIG_TRUE)
        {
          if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, i_k);
          if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, j_k);
          btor_add_sat (smgr, -d_k);
          btor_add_sat (smgr, 0);
        }
        if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_FALSE)
        {
          if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, -i_k);
          if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, -j_k);
          btor_add_sat (smgr, -d_k);
          btor_add_sat (smgr, 0);
        }
      }
    }
    while (!BTOR_EMPTY_STACK (diffs))
    {
      k = BTOR_POP_STACK (diffs);
      assert (k != 0);
      btor_add_sat (smgr, k);
    }
    BTOR_RELEASE_STACK (mm, diffs);
  }
  e = btor_next_cnf_id_sat_mgr (smgr);
  assert (e != 0);
  btor_add_sat (smgr, e);
  btor_add_sat (smgr, 0);
  assert (av_var1->len == av_var2->len);
  len = av_var1->len;
  for (k = 0; k < len; k++)
  {
    aig1 = av_var1->aigs[k];
    aig2 = av_var2->aigs[k];
    assert (!BTOR_IS_CONST_AIG (aig1));
    assert (!BTOR_IS_INVERTED_AIG (aig1));
    assert (!BTOR_IS_CONST_AIG (aig2));
    assert (!BTOR_IS_INVERTED_AIG (aig2));
    if (aig1->cnf_id == 0) aig1->cnf_id = btor_next_cnf_id_sat_mgr (smgr);
    a_k = aig1->cnf_id;
    assert (a_k != 0);
    if (aig2->cnf_id == 0) aig2->cnf_id = btor_next_cnf_id_sat_mgr (smgr);
    b_k = aig2->cnf_id;
    assert (b_k != 0);
    btor_add_sat (smgr, -e);
    btor_add_sat (smgr, a_k);
    btor_add_sat (smgr, -b_k);
    btor_add_sat (smgr, 0);
    btor_add_sat (smgr, -e);
    btor_add_sat (smgr, -a_k);
    btor_add_sat (smgr, b_k);
    btor_add_sat (smgr, 0);
  }
  btor_release_delete_aigvec (emgr->avmgr, av_index1);
  btor_release_delete_aigvec (emgr->avmgr, av_index2);
}

static void
register_read (BtorExpMgr *emgr, BtorExp *array, BtorExp *var, BtorExp *index)
{
  BtorReadObj **cur          = NULL;
  BtorReadObj *obj           = NULL;
  BtorReadObjPtrStack *stack = NULL;
  assert (emgr != NULL);
  assert (array != NULL);
  assert (var != NULL);
  assert (index != NULL);
  assert (!BTOR_IS_INVERTED_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  if (emgr->read_enc == BTOR_EAGER_READ_ENC)
  {
    stack = array->read_constraint;
    for (cur = (*stack).start; cur != (*stack).top; cur++)
    {
      obj = *cur;
      encode_read (emgr, obj->index, index, obj->var, var);
    }
    obj = new_read_obj (emgr, var, index);
    BTOR_PUSH_STACK (emgr->mm, *array->read_constraint, obj);
  }
}

/*------------------------------------------------------------------------*/
/* BtorExp                                                                */
/*------------------------------------------------------------------------*/

static BtorExp *
zeros_exp (BtorExpMgr *emgr, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string = zeros_string (emgr, len);
  result = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

static BtorExp *
ones_exp (BtorExpMgr *emgr, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string = ones_string (emgr, len);
  result = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

static BtorExp *
one_exp (BtorExpMgr *emgr, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string                      = zeros_string (emgr, len);
  string[strlen (string) - 1] = '1';
  result                      = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

static BtorExp *
int_min_exp (BtorExpMgr *emgr, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 1);
  string    = zeros_string (emgr, len);
  string[0] = '1';
  result    = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

static BtorExp *
int_to_exp (BtorExpMgr *emgr, int x, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (x >= 0);
  assert (len > 1);
  string = int_to_string (emgr, x, len);
  result = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

static void
connect_child_exp (BtorExpMgr *emgr, BtorExp *parent, BtorExp *child, int pos)
{
  BtorExp *real_parent   = NULL;
  BtorExp *real_child    = NULL;
  BtorExp *last_parent   = NULL;
  BtorExp *tagged_parent = NULL;
  int i                  = 0;
  assert (emgr != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (pos >= 0);
  assert (pos <= 2);
  real_parent         = BTOR_REAL_ADDR_EXP (parent);
  real_child          = BTOR_REAL_ADDR_EXP (child);
  real_parent->e[pos] = child;
  tagged_parent       = BTOR_TAG_EXP (real_parent, pos);
  /* no parent so far? */
  if (real_child->first_parent == NULL)
  {
    assert (real_child->last_parent == NULL);
    real_child->first_parent = tagged_parent;
    assert (real_parent->prev_parent[pos] == NULL);
    assert (real_parent->next_parent[pos] == NULL);
  }
  /* append parent to list */
  else
  {
    last_parent = real_child->last_parent;
    assert (last_parent != NULL);
    real_parent->prev_parent[pos] = last_parent;
    i                             = BTOR_GET_TAG_EXP (last_parent);
    BTOR_REAL_ADDR_EXP (last_parent)->next_parent[i] = tagged_parent;
  }
  real_child->last_parent = tagged_parent;
}

#define BTOR_NEXT_PARENT(exp) \
  (BTOR_REAL_ADDR_EXP (exp)->next_parent[BTOR_GET_TAG_EXP (exp)])
#define BTOR_PREV_PARENT(exp) \
  (BTOR_REAL_ADDR_EXP (exp)->prev_parent[BTOR_GET_TAG_EXP (exp)])

static void
disconnect_child_exp (BtorExpMgr *emgr, BtorExp *parent, int pos)
{
  BtorExp *real_parent       = NULL;
  BtorExp *first_parent      = NULL;
  BtorExp *last_parent       = NULL;
  BtorExp *real_first_parent = NULL;
  BtorExp *real_last_parent  = NULL;
  BtorExp *real_child        = NULL;
  assert (emgr != NULL);
  assert (parent != NULL);
  assert (pos >= 0);
  assert (pos <= 2);
  assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (parent)));
  assert (!BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (parent)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (parent)));
  real_parent  = BTOR_REAL_ADDR_EXP (parent);
  parent       = BTOR_TAG_EXP (real_parent, pos);
  real_child   = BTOR_REAL_ADDR_EXP (real_parent->e[pos]);
  first_parent = real_child->first_parent;
  last_parent  = real_child->last_parent;
  assert (first_parent != NULL);
  assert (last_parent != NULL);
  real_first_parent = BTOR_REAL_ADDR_EXP (first_parent);
  real_last_parent  = BTOR_REAL_ADDR_EXP (last_parent);
  /* only one parent? */
  if (first_parent == parent && first_parent == last_parent)
  {
    assert (real_parent->next_parent[pos] == NULL);
    assert (real_parent->prev_parent[pos] == NULL);
    real_child->first_parent = NULL;
    real_child->last_parent  = NULL;
  }
  /* is parent first parent in the list? */
  else if (first_parent == parent)
  {
    assert (real_parent->next_parent[pos] != NULL);
    assert (real_parent->prev_parent[pos] == NULL);
    real_child->first_parent                    = real_parent->next_parent[pos];
    BTOR_PREV_PARENT (real_child->first_parent) = NULL;
  }
  /* is parent last parent in the list? */
  else if (last_parent == parent)
  {
    assert (real_parent->next_parent[pos] == NULL);
    assert (real_parent->prev_parent[pos] != NULL);
    real_child->last_parent                    = real_parent->prev_parent[pos];
    BTOR_NEXT_PARENT (real_child->last_parent) = NULL;
  }
  /* hang out parent from list */
  else
  {
    assert (real_parent->next_parent[pos] != NULL);
    assert (real_parent->prev_parent[pos] != NULL);
    BTOR_PREV_PARENT (real_parent->next_parent[pos]) =
        real_parent->prev_parent[pos];
    BTOR_NEXT_PARENT (real_parent->prev_parent[pos]) =
        real_parent->next_parent[pos];
  }
  real_parent->next_parent[pos] = NULL;
  real_parent->prev_parent[pos] = NULL;
  real_parent->e[pos]           = NULL;
}

static BtorExp *
new_const_exp_node (BtorExpMgr *emgr, const char *bits)
{
  BtorExp *exp = NULL;
  int i        = 0;
  int len      = 0;
  assert (emgr != NULL);
  assert (bits != NULL);
  len = strlen (bits);
  assert (len > 0);
  exp       = (BtorExp *) btor_calloc (emgr->mm, 1, sizeof (BtorExp));
  exp->kind = BTOR_CONST_EXP;
  exp->bits = btor_malloc (emgr->mm, sizeof (char) * (len + 1));
  for (i = 0; i < len; i++) exp->bits[i] = bits[i] == '1' ? '1' : '0';
  exp->bits[len] = '\0';
  exp->len       = len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  return exp;
}

static BtorExp *
new_slice_exp_node (BtorExpMgr *emgr, BtorExp *e0, int upper, int lower)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (lower >= 0);
  assert (upper >= lower);
  BtorExp *exp = NULL;
  exp          = (BtorExp *) btor_calloc (emgr->mm, 1, sizeof (BtorExp));
  exp->kind    = BTOR_SLICE_EXP;
  exp->upper   = upper;
  exp->lower   = lower;
  exp->len     = upper - lower + 1;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  connect_child_exp (emgr, exp, e0, 0);
  return exp;
}

static BtorExp *
new_binary_exp_node (
    BtorExpMgr *emgr, BtorExpKind kind, BtorExp *e0, BtorExp *e1, int len)
{
  BtorExp *exp = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (len > 0);
  exp       = (BtorExp *) btor_calloc (emgr->mm, 1, sizeof (BtorExp));
  exp->kind = kind;
  exp->len  = len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  connect_child_exp (emgr, exp, e0, 0);
  connect_child_exp (emgr, exp, e1, 1);
  return exp;
}

static BtorExp *
new_ternary_exp_node (BtorExpMgr *emgr,
                      BtorExpKind kind,
                      BtorExp *e0,
                      BtorExp *e1,
                      BtorExp *e2,
                      int len)
{
  BtorExp *exp = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  assert (len > 0);
  exp       = (BtorExp *) btor_calloc (emgr->mm, 1, sizeof (BtorExp));
  exp->kind = kind;
  exp->len  = len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  connect_child_exp (emgr, exp, e0, 0);
  connect_child_exp (emgr, exp, e1, 1);
  connect_child_exp (emgr, exp, e2, 2);
  return exp;
}

static void
delete_exp_node (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));
  if (BTOR_IS_CONST_EXP (exp))
  {
    btor_freestr (emgr->mm, exp->bits);
  }
  else if (BTOR_IS_VAR_EXP (exp))
  {
    btor_freestr (emgr->mm, exp->symbol);
    if (exp->assignment != NULL) btor_freestr (emgr->mm, exp->assignment);
  }
  else if (BTOR_IS_ARRAY_EXP (exp))
  {
    assert (BTOR_COUNT_STACK (*exp->read_constraint) == 0);
    BTOR_RELEASE_STACK (emgr->mm, *exp->read_constraint);
    btor_free (emgr->mm, exp->read_constraint, sizeof (BtorExpPtrStack));
  }
  else if (BTOR_IS_UNARY_EXP (exp))
  {
    disconnect_child_exp (emgr, exp, 0);
  }
  else if (BTOR_IS_BINARY_EXP (exp))
  {
    disconnect_child_exp (emgr, exp, 0);
    disconnect_child_exp (emgr, exp, 1);
  }
  else
  {
    assert (BTOR_IS_TERNARY_EXP (exp));
    disconnect_child_exp (emgr, exp, 0);
    disconnect_child_exp (emgr, exp, 1);
    disconnect_child_exp (emgr, exp, 2);
  }
  if (exp->av != NULL)
  {
    assert (emgr->avmgr != NULL);
    btor_release_delete_aigvec (emgr->avmgr, exp->av);
  }
  btor_free (emgr->mm, exp, sizeof (BtorExp));
}

static unsigned int
compute_exp_hash (BtorExp *exp, int table_size)
{
  unsigned int hash = 0;
  int i             = 0;
  int len           = 0;
  assert (exp != NULL);
  assert (table_size > 0);
  assert (btor_is_power_of_2_util (table_size));
  assert (!BTOR_IS_INVERTED_EXP (exp));
  assert (!BTOR_IS_VAR_EXP (exp));
  assert (!BTOR_IS_ARRAY_EXP (exp));
  if (BTOR_IS_CONST_EXP (exp))
  {
    len = exp->len;
    for (i = 0; i < len; i++)
    {
      if (exp->bits[i] == '1') hash += 1u << (i % 32);
    }
  }
  else if (BTOR_IS_UNARY_EXP (exp))
  {
    hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id;
    if (exp->kind == BTOR_SLICE_EXP)
      hash += (unsigned int) exp->upper + (unsigned int) exp->lower;
  }
  else if (BTOR_IS_BINARY_EXP (exp))
  {
    hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[1])->id;
  }
  else
  {
    assert (BTOR_IS_TERNARY_EXP (exp));
    hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[1])->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[2])->id;
  }
  hash = (hash * BTOR_EXP_UNIQUE_TABLE_PRIME) & (table_size - 1);
  return hash;
}

static BtorExp **
find_const_exp (BtorExpMgr *emgr, const char *bits)
{
  BtorExp *cur      = NULL;
  BtorExp **result  = NULL;
  unsigned int hash = 0u;
  int i             = 0;
  int len           = 0;
  assert (emgr != NULL);
  assert (bits != NULL);
  len = strlen (bits);
  for (i = 0; i < len; i++)
  {
    if (bits[i] == '1') hash += 1u << (i % 32);
  }
  hash   = (hash * BTOR_EXP_UNIQUE_TABLE_PRIME) & (emgr->table.size - 1);
  result = emgr->table.chains + hash;
  cur    = *result;
  while (cur != NULL)
  {
    assert (!BTOR_IS_INVERTED_EXP (cur));
    if (BTOR_IS_CONST_EXP (cur) && cur->len == len
        && strcmp (cur->bits, bits) == 0)
    {
      break;
    }
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

static BtorExp **
find_slice_exp (BtorExpMgr *emgr, BtorExp *e0, int upper, int lower)
{
  BtorExp *cur      = NULL;
  BtorExp **result  = NULL;
  unsigned int hash = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (lower >= 0);
  assert (upper >= lower);
  hash = (((unsigned int) BTOR_REAL_ADDR_EXP (e0)->id + (unsigned int) upper
           + (unsigned int) lower)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (emgr->table.size - 1);
  result = emgr->table.chains + hash;
  cur    = *result;
  while (cur != NULL)
  {
    assert (!BTOR_IS_INVERTED_EXP (cur));
    if (cur->kind == BTOR_SLICE_EXP && cur->e[0] == e0 && cur->upper == upper
        && cur->lower == lower)
    {
      break;
    }
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}
static BtorExp **
find_binary_exp (BtorExpMgr *emgr, BtorExpKind kind, BtorExp *e0, BtorExp *e1)
{
  BtorExp *cur      = NULL;
  BtorExp **result  = NULL;
  BtorExp *temp     = NULL;
  unsigned int hash = 0;
  assert (emgr != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  hash = (((unsigned int) BTOR_REAL_ADDR_EXP (e0)->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (e1)->id)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (emgr->table.size - 1);
  result = emgr->table.chains + hash;
  cur    = *result;
  if (BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
      && BTOR_REAL_ADDR_EXP (e1)->id < BTOR_REAL_ADDR_EXP (e0)->id)
  {
    temp = e0;
    e0   = e1;
    e1   = temp;
  }
  while (cur != NULL)
  {
    assert (!BTOR_IS_INVERTED_EXP (cur));
    if (cur->kind == kind && cur->e[0] == e0 && cur->e[1] == e1)
    {
      break;
    }
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

static BtorExp **
find_ternary_exp (
    BtorExpMgr *emgr, BtorExpKind kind, BtorExp *e0, BtorExp *e1, BtorExp *e2)
{
  BtorExp *cur      = NULL;
  BtorExp **result  = NULL;
  unsigned int hash = 0;
  assert (emgr != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  hash = (((unsigned) BTOR_REAL_ADDR_EXP (e0)->id
           + (unsigned) BTOR_REAL_ADDR_EXP (e1)->id
           + (unsigned) BTOR_REAL_ADDR_EXP (e2)->id)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (emgr->table.size - 1);
  result = emgr->table.chains + hash;
  cur    = *result;
  while (cur != NULL)
  {
    assert (!BTOR_IS_INVERTED_EXP (cur));
    if (cur->kind == kind && cur->e[0] == e0 && cur->e[1] == e1
        && cur->e[2] == e2)
    {
      break;
    }
    else
    {
      result = &(cur->next);
      cur    = *result;
    }
  }
  return result;
}

static void
enlarge_exp_unique_table (BtorExpMgr *emgr)
{
  BtorExp **new_chains = NULL;
  int new_size         = 0;
  int i                = 0;
  int size             = 0;
  unsigned int hash    = 0u;
  BtorExp *cur         = NULL;
  BtorExp *temp        = NULL;
  assert (emgr != NULL);
  size     = emgr->table.size;
  new_size = size << 1;
  assert (new_size / size == 2);
  new_chains = (BtorExp **) btor_calloc (
      emgr->mm, (size_t) new_size, sizeof (BtorExp *));
  for (i = 0; i < size; i++)
  {
    cur = emgr->table.chains[i];
    while (cur != NULL)
    {
      assert (!BTOR_IS_INVERTED_EXP (cur));
      assert (!BTOR_IS_VAR_EXP (cur));
      assert (!BTOR_IS_ARRAY_EXP (cur));
      temp             = cur->next;
      hash             = compute_exp_hash (cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur;
      cur              = temp;
    }
  }
  btor_free (emgr->mm, emgr->table.chains, sizeof (BtorExp *) * size);
  emgr->table.size   = new_size;
  emgr->table.chains = new_chains;
}

static void
delete_exp_unique_table_entry (BtorExpMgr *emgr, BtorExp *exp)
{
  unsigned int hash = 0u;
  BtorExp *cur      = NULL;
  BtorExp *prev     = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));
  hash = compute_exp_hash (exp, emgr->table.size);
  cur  = emgr->table.chains[hash];
  while (cur != exp && cur != NULL)
  {
    assert (!BTOR_IS_INVERTED_EXP (cur));
    prev = cur;
    cur  = cur->next;
  }
  assert (cur != NULL);
  if (prev == NULL)
    emgr->table.chains[hash] = cur->next;
  else
    prev->next = cur->next;
  emgr->table.num_elements--;
  delete_exp_node (emgr, cur);
}

static void
inc_exp_ref_counter (BtorExp *exp)
{
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->refs < INT_MAX);
  BTOR_REAL_ADDR_EXP (exp)->refs++;
}

BtorExp *
btor_copy_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  inc_exp_ref_counter (exp);
  return exp;
}

void
btor_mark_exp (BtorExpMgr *emgr, BtorExp *exp, int new_mark)
{
  BtorExpPtrStack stack;
  BtorExp *cur = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (emgr->mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    if (cur->mark != new_mark)
    {
      cur->mark = new_mark;
      if (BTOR_IS_UNARY_EXP (cur))
      {
        BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
      }
      else if (BTOR_IS_BINARY_EXP (cur))
      {
        BTOR_PUSH_STACK (emgr->mm, stack, cur->e[1]);
        BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
      }
      else if (BTOR_IS_TERNARY_EXP (cur))
      {
        BTOR_PUSH_STACK (emgr->mm, stack, cur->e[2]);
        BTOR_PUSH_STACK (emgr->mm, stack, cur->e[1]);
        BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
      }
    }
  }
  BTOR_RELEASE_STACK (emgr->mm, stack);
}

void
btor_release_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExpPtrStack stack;
  BtorExp *cur = BTOR_REAL_ADDR_EXP (exp);
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (cur->refs > 0);
  if (cur->refs > 1)
  {
    if (!BTOR_IS_VAR_EXP (cur) && !BTOR_IS_ARRAY_EXP (cur)) cur->refs--;
  }
  else
  {
    assert (cur->refs == 1);
    BTOR_INIT_STACK (stack);
    BTOR_PUSH_STACK (emgr->mm, stack, cur);
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
      if (cur->refs > 1)
      {
        if (!BTOR_IS_VAR_EXP (cur) && !BTOR_IS_ARRAY_EXP (cur)) cur->refs--;
      }
      else
      {
        assert (cur->refs == 1);
        if (BTOR_IS_UNARY_EXP (cur))
        {
          BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
        }
        else if (BTOR_IS_BINARY_EXP (cur))
        {
          BTOR_PUSH_STACK (emgr->mm, stack, cur->e[1]);
          BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
        }
        else if (BTOR_IS_TERNARY_EXP (cur))
        {
          BTOR_PUSH_STACK (emgr->mm, stack, cur->e[2]);
          BTOR_PUSH_STACK (emgr->mm, stack, cur->e[1]);
          BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
        }
        if (!BTOR_IS_VAR_EXP (cur) && !BTOR_IS_ARRAY_EXP (cur))
          delete_exp_unique_table_entry (emgr, cur);
      }
    }
    BTOR_RELEASE_STACK (emgr->mm, stack);
  }
}

BtorExp *
btor_const_exp (BtorExpMgr *emgr, const char *bits)
{
  BtorExp **lookup = NULL;
  assert (emgr != NULL);
  assert (bits != NULL);
  assert (strlen (bits) > 0);
  lookup = find_const_exp (emgr, bits);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_const_exp (emgr, bits);
    }
    *lookup = new_const_exp_node (emgr, bits);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
  }
  else
  {
    inc_exp_ref_counter (*lookup);
  }
  assert (!BTOR_IS_INVERTED_EXP (*lookup));
  return *lookup;
}

BtorExp *
btor_zero_exp (BtorExpMgr *emgr, int len)
{
  assert (len > 0);
  return zeros_exp (emgr, len);
}

BtorExp *
btor_var_exp (BtorExpMgr *emgr, int len, const char *symbol)
{
  BtorExp *exp = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  assert (symbol != NULL);
  exp       = (BtorExp *) btor_calloc (emgr->mm, 1, sizeof (BtorExp));
  exp->kind = BTOR_VAR_EXP;
  exp->symbol =
      (char *) btor_malloc (emgr->mm, sizeof (char) * (strlen (symbol) + 1));
  strcpy (exp->symbol, symbol);
  exp->len = len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  BTOR_PUSH_STACK (emgr->mm, emgr->vars, exp);
  return exp;
}

BtorExp *
btor_array_exp (BtorExpMgr *emgr, int elem_len, int index_len)
{
  BtorExp *exp = NULL;
  assert (emgr != NULL);
  assert (elem_len > 0);
  assert (index_len > 0);
  assert (index_len <= 30);
  exp       = (BtorExp *) btor_calloc (emgr->mm, 1, sizeof (BtorExp));
  exp->kind = BTOR_ARRAY_EXP;
  exp->read_constraint = (BtorReadObjPtrStack *) btor_malloc (
      emgr->mm, sizeof (BtorReadObjPtrStack));
  BTOR_INIT_STACK (*exp->read_constraint);
  exp->index_len = index_len;
  exp->len       = elem_len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  BTOR_PUSH_STACK (emgr->mm, emgr->arrays, exp);
  return exp;
}

static BtorExp *
slice_exp (BtorExpMgr *emgr, BtorExp *exp, int upper, int lower)
{
  BtorExp **lookup = NULL;
  BtorExp *node    = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);
  lookup = find_slice_exp (emgr, exp, upper, lower);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_slice_exp (emgr, exp, upper, lower);
    }
    *lookup = new_slice_exp_node (emgr, exp, upper, lower);
    inc_exp_ref_counter (exp);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
    node = *lookup;
  }
  else
  {
    inc_exp_ref_counter (*lookup);
  }
  assert (!BTOR_IS_INVERTED_EXP (*lookup));
  return *lookup;
}

static BtorExp *
rewrite_exp (BtorExpMgr *emgr,
             BtorExpKind kind,
             BtorExp *e0,
             BtorExp *e1,
             BtorExp *e2,
             int upper,
             int lower)
{
  BtorExp *result   = NULL;
  BtorExp *real_e0  = NULL;
  BtorExp *real_e1  = NULL;
  BtorExp *real_e2  = NULL;
  BtorExp *temp     = NULL;
  char *bits_result = NULL;
  char *bits_e0     = NULL;
  char *bits_e1     = NULL;
  int i             = 0;
  int diff          = 0;
  int len           = 0;
  int counter       = 0;
  int is_zero       = 0;
  int is_one        = 0;
  assert (emgr != NULL);
  assert (emgr->rewrite_level > 0);
  assert (emgr->rewrite_level <= 2);
  assert (lower >= 0);
  assert (lower <= upper);
  if (BTOR_IS_UNARY_EXP_KIND (kind))
  {
    assert (e0 != NULL);
    assert (e1 == NULL);
    assert (e2 == NULL);
    assert (kind == BTOR_SLICE_EXP);
    if (emgr->dump_trace)
    {
      /* TODO */
    }
    else
    {
      real_e0 = BTOR_REAL_ADDR_EXP (e0);
      diff    = upper - lower;
      if (diff + 1 == real_e0->len)
      {
        result = btor_copy_exp (emgr, e0);
      }
      else if (BTOR_IS_CONST_EXP (real_e0))
      {
        counter = 0;
        len     = real_e0->len;
        bits_result =
            (char *) btor_malloc (emgr->mm, sizeof (char) * (diff + 2));
        for (i = len - upper - 1; i <= len - upper - 1 + diff; i++)
          bits_result[counter++] = real_e0->bits[i];
        bits_result[counter] = '\0';
        result               = btor_const_exp (emgr, bits_result);
        result               = BTOR_COND_INVERT_EXP (e0, result);
        btor_delete_const (emgr->mm, bits_result);
      }
    }
  }
  else if (BTOR_IS_BINARY_EXP_KIND (kind))
  {
    assert (e0 != NULL);
    assert (e1 != NULL);
    assert (e2 == NULL);
    real_e0 = BTOR_REAL_ADDR_EXP (e0);
    real_e1 = BTOR_REAL_ADDR_EXP (e1);
    if (emgr->dump_trace)
    {
      /* TODO */
    }
    else
    {
      if (BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1))
      {
        if (BTOR_IS_INVERTED_EXP (e0))
          bits_e0 = btor_not_const (emgr->mm, real_e0->bits);
        else
          bits_e0 = btor_copy_const (emgr->mm, real_e0->bits);
        if (BTOR_IS_INVERTED_EXP (e1))
          bits_e1 = btor_not_const (emgr->mm, real_e1->bits);
        else
          bits_e1 = btor_copy_const (emgr->mm, real_e1->bits);
        switch (kind)
        {
          case BTOR_AND_EXP:
            bits_result = btor_and_const (emgr->mm, bits_e0, bits_e1);
            break;
          case BTOR_EQ_EXP:
            bits_result = btor_eq_const (emgr->mm, bits_e0, bits_e1);
            break;
          case BTOR_ADD_EXP:
            bits_result = btor_add_const (emgr->mm, bits_e0, bits_e1);
            break;
          case BTOR_UMUL_EXP:
            bits_result = btor_umul_const (emgr->mm, bits_e0, bits_e1);
            break;
          case BTOR_ULT_EXP:
            bits_result = btor_ult_const (emgr->mm, bits_e0, bits_e1);
            break;
          case BTOR_UDIV_EXP:
            bits_result = btor_udiv_const (emgr->mm, bits_e0, bits_e1);
            break;
          case BTOR_UMOD_EXP:
            bits_result = btor_umod_const (emgr->mm, bits_e0, bits_e1);
            break;
          case BTOR_SLL_EXP:
            bits_result = btor_sll_const (emgr->mm, bits_e0, bits_e1);
            break;
          case BTOR_SRL_EXP:
            bits_result = btor_srl_const (emgr->mm, bits_e0, bits_e1);
            break;
          default:
            assert (kind == BTOR_CONCAT_EXP);
            bits_result = btor_concat_const (emgr->mm, bits_e0, bits_e1);
            break;
        }
        result = btor_const_exp (emgr, bits_result);
        btor_delete_const (emgr->mm, bits_result);
        btor_delete_const (emgr->mm, bits_e1);
        btor_delete_const (emgr->mm, bits_e0);
      }
      else if (BTOR_IS_CONST_EXP (real_e0) && !BTOR_IS_CONST_EXP (real_e1))
      {
        if (BTOR_IS_INVERTED_EXP (e0))
          bits_e0 = btor_not_const (emgr->mm, real_e0->bits);
        else
          bits_e0 = btor_copy_const (emgr->mm, real_e0->bits);
        /* TODO: AND_EXP EQ_EXP */
        is_zero = is_zero_string (emgr, bits_e0, real_e0->len);
        is_one  = is_one_string (emgr, bits_e0, real_e0->len);
        if (is_zero)
        {
          if (kind == BTOR_ADD_EXP)
            result = btor_copy_exp (emgr, e1);
          else if (kind == BTOR_UMUL_EXP || kind == BTOR_SLL_EXP
                   || kind == BTOR_SRL_EXP || kind == BTOR_UDIV_EXP
                   || kind == BTOR_UMOD_EXP)
            result = zeros_exp (emgr, real_e0->len);
        }
        else if (is_one)
        {
          if (kind == BTOR_UMUL_EXP) result = btor_copy_exp (emgr, e1);
        }
        btor_delete_const (emgr->mm, bits_e0);
      }
      else if (!BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1))
      {
        if (BTOR_IS_INVERTED_EXP (e1))
          bits_e1 = btor_not_const (emgr->mm, real_e1->bits);
        else
          bits_e1 = btor_copy_const (emgr->mm, real_e1->bits);
        /* TODO: AND_EXP EQ_EXP */
        is_zero = is_zero_string (emgr, bits_e1, real_e1->len);
        is_one  = is_one_string (emgr, bits_e1, real_e1->len);
        if (is_zero)
        {
          if (kind == BTOR_ADD_EXP)
            result = btor_copy_exp (emgr, e0);
          else if (kind == BTOR_UMUL_EXP || kind == BTOR_SLL_EXP
                   || kind == BTOR_SRL_EXP)
            result = zeros_exp (emgr, real_e0->len);
          else if (kind == BTOR_UDIV_EXP)
            result = ones_exp (emgr, real_e0->len);
          else if (kind == BTOR_UMOD_EXP)
            result = btor_copy_exp (emgr, e0);
        }
        else if (is_one)
        {
          if (kind == BTOR_UMUL_EXP) result = btor_copy_exp (emgr, e0);
        }
        btor_delete_const (emgr->mm, bits_e1);
      }
      else if (real_e0 == real_e1
               && (kind == BTOR_EQ_EXP || kind == BTOR_ADD_EXP))
      {
        if (kind == BTOR_EQ_EXP)
        {
          if (e0 == e1)
            result = one_exp (emgr, 1);
          else
            result = zeros_exp (emgr, 1);
        }
        else
        {
          assert (kind == BTOR_ADD_EXP);
          /* replace x + x by x * 2 */
          if (e0 == e1)
          {
            if (real_e0->len >= 2)
            {
              temp   = int_to_exp (emgr, 2, real_e0->len);
              result = btor_umul_exp (emgr, e0, temp);
              btor_release_exp (emgr, temp);
            }
          }
          else
          /* replace x + ~x by -1 */
          {
            result = ones_exp (emgr, real_e0->len);
          }
        }
      }
      else if (e0 == e1
               && (kind == BTOR_ULT_EXP || kind == BTOR_UDIV_EXP
                   || kind == BTOR_UMOD_EXP))
      {
        switch (kind)
        {
          case BTOR_ULT_EXP: result = zeros_exp (emgr, 1); break;
          case BTOR_UDIV_EXP: result = one_exp (emgr, real_e0->len); break;
          default:
            assert (kind == BTOR_UMOD_EXP);
            result = zeros_exp (emgr, real_e0->len);
            break;
        }
      }
    }
  }
  else
  {
    assert (BTOR_IS_TERNARY_EXP_KIND (kind));
    assert (e0 != NULL);
    assert (e1 != NULL);
    assert (e2 != NULL);
    assert (kind == BTOR_COND_EXP);
    real_e0 = BTOR_REAL_ADDR_EXP (e0);
    real_e1 = BTOR_REAL_ADDR_EXP (e1);
    real_e2 = BTOR_REAL_ADDR_EXP (e2);
    if (emgr->dump_trace)
    {
      /* TODO */
    }
    else
    {
      if (BTOR_IS_CONST_EXP (real_e0))
      {
        if ((!BTOR_IS_INVERTED_EXP (e0) && e0->bits[0] == '1')
            || (BTOR_IS_INVERTED_EXP (e0) && real_e0->bits[0] == '0'))
          result = btor_copy_exp (emgr, e1);
        else
          result = btor_copy_exp (emgr, e2);
      }
      else if (e1 == e2)
      {
        result = btor_copy_exp (emgr, e1);
      }
      result = BTOR_COND_INVERT_EXP (e0, result);
    }
  }
  return result;
}

BtorExp *
btor_not_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  inc_exp_ref_counter (exp);
  return BTOR_INVERT_EXP (exp);
}

BtorExp *
btor_neg_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result = NULL;
  BtorExp *one    = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  one    = one_exp (emgr, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_add_exp (emgr, BTOR_INVERT_EXP (exp), one);
  btor_release_exp (emgr, one);
  return result;
}

BtorExp *
btor_nego_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result   = NULL;
  BtorExp *sign_exp = NULL;
  BtorExp *rest     = NULL;
  BtorExp *zeros    = NULL;
  BtorExp *eq       = NULL;
  int len           = 0;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 1);
  len      = BTOR_REAL_ADDR_EXP (exp)->len;
  sign_exp = btor_slice_exp (emgr, exp, len - 1, len - 1);
  rest     = btor_slice_exp (emgr, exp, len - 2, 0);
  zeros    = zeros_exp (emgr, len - 1);
  eq       = btor_eq_exp (emgr, rest, zeros);
  result   = btor_and_exp (emgr, sign_exp, eq);
  btor_release_exp (emgr, sign_exp);
  btor_release_exp (emgr, rest);
  btor_release_exp (emgr, zeros);
  btor_release_exp (emgr, eq);
  return result;
}

BtorExp *
btor_redor_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result = NULL;
  BtorExp *zeros  = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 1);
  zeros  = zeros_exp (emgr, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_ne_exp (emgr, exp, zeros);
  btor_release_exp (emgr, zeros);
  return result;
}

BtorExp *
btor_redxor_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result = NULL;
  BtorExp *slice  = NULL;
  BtorExp * xor   = NULL;
  int i           = 0;
  int len         = 0;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 1);
  len    = BTOR_REAL_ADDR_EXP (exp)->len;
  result = btor_slice_exp (emgr, exp, 0, 0);
  for (i = 1; i < len; i++)
  {
    slice = btor_slice_exp (emgr, exp, i, i);
    xor   = btor_xor_exp (emgr, result, slice);
    btor_release_exp (emgr, slice);
    btor_release_exp (emgr, result);
    result = xor;
  }
  return result;
}

BtorExp *
btor_redand_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result = NULL;
  BtorExp *ones   = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 1);
  ones   = ones_exp (emgr, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_eq_exp (emgr, exp, ones);
  btor_release_exp (emgr, ones);
  return result;
}

BtorExp *
btor_slice_exp (BtorExpMgr *emgr, BtorExp *exp, int upper, int lower)
{
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_SLICE_EXP, exp, NULL, NULL, upper, lower);
  if (result == NULL) result = slice_exp (emgr, exp, upper, lower);
  return result;
}

BtorExp *
btor_uext_exp (BtorExpMgr *emgr, BtorExp *exp, int len)
{
  BtorExp *result = NULL;
  BtorExp *zeros  = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  assert (len >= 0);
  if (len == 0)
  {
    inc_exp_ref_counter (exp);
    result = exp;
  }
  else
  {
    assert (len > 0);
    zeros  = zeros_exp (emgr, len);
    result = btor_concat_exp (emgr, zeros, exp);
    btor_release_exp (emgr, zeros);
  }
  return result;
}

BtorExp *
btor_sext_exp (BtorExpMgr *emgr, BtorExp *exp, int len)
{
  BtorExp *result = NULL;
  BtorExp *zeros  = NULL;
  BtorExp *ones   = NULL;
  BtorExp *neg    = NULL;
  BtorExp *cond   = NULL;
  int exp_len     = 0;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  assert (len >= 0);
  if (len == 0)
  {
    inc_exp_ref_counter (exp);
    result = exp;
  }
  else
  {
    assert (len > 0);
    zeros   = zeros_exp (emgr, len);
    ones    = ones_exp (emgr, len);
    exp_len = BTOR_REAL_ADDR_EXP (exp)->len;
    neg     = btor_slice_exp (emgr, exp, exp_len - 1, exp_len - 1);
    cond    = btor_cond_exp (emgr, neg, ones, zeros);
    result  = btor_concat_exp (emgr, cond, exp);
    btor_release_exp (emgr, zeros);
    btor_release_exp (emgr, ones);
    btor_release_exp (emgr, neg);
    btor_release_exp (emgr, cond);
  }
  return result;
}

static BtorExp *
btor_binary_exp (
    BtorExpMgr *emgr, BtorExpKind kind, BtorExp *e0, BtorExp *e1, int len)
{
  BtorExp **lookup = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (len > 0);
  lookup = find_binary_exp (emgr, kind, e0, e1);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_binary_exp (emgr, kind, e0, e1);
    }
    if (BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
        && BTOR_REAL_ADDR_EXP (e1)->id < BTOR_REAL_ADDR_EXP (e0)->id)
      *lookup = new_binary_exp_node (emgr, kind, e1, e0, len);
    else
      *lookup = new_binary_exp_node (emgr, kind, e0, e1, len);
    inc_exp_ref_counter (e0);
    inc_exp_ref_counter (e1);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
  }
  else
  {
    inc_exp_ref_counter (*lookup);
  }
  assert (!BTOR_IS_INVERTED_EXP (*lookup));
  return *lookup;
}

BtorExp *
btor_or_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (
      btor_and_exp (emgr, BTOR_INVERT_EXP (e0), BTOR_INVERT_EXP (e1)));
}

BtorExp *
btor_implies_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (btor_and_exp (emgr, e0, BTOR_INVERT_EXP (e1)));
}

BtorExp *
btor_xor_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp * or    = NULL;
  BtorExp *and    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  or     = btor_or_exp (emgr, e0, e1);
  and    = btor_and_exp (emgr, e0, e1);
  result = btor_and_exp (emgr, or, BTOR_INVERT_EXP (and));
  btor_release_exp (emgr, or);
  btor_release_exp (emgr, and);
  return result;
}

BtorExp *
btor_xnor_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (btor_xor_exp (emgr, e0, e1));
}

BtorExp *
btor_and_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_AND_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL)
    result = btor_binary_exp (emgr, BTOR_AND_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_eq_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_EQ_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = btor_binary_exp (emgr, BTOR_EQ_EXP, e0, e1, 1);
  return result;
}

BtorExp *
btor_ne_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (btor_eq_exp (emgr, e0, e1));
}

BtorExp *
btor_add_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_ADD_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL)
    result = btor_binary_exp (emgr, BTOR_ADD_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_uaddo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result  = NULL;
  BtorExp *uext_e1 = NULL;
  BtorExp *uext_e2 = NULL;
  BtorExp *add     = NULL;
  int len          = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  uext_e1 = btor_uext_exp (emgr, e0, 1);
  uext_e2 = btor_uext_exp (emgr, e1, 1);
  add     = btor_add_exp (emgr, uext_e1, uext_e2);
  result  = btor_slice_exp (emgr, add, len, len);
  btor_release_exp (emgr, uext_e1);
  btor_release_exp (emgr, uext_e2);
  btor_release_exp (emgr, add);
  return result;
}

BtorExp *
btor_saddo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result      = NULL;
  BtorExp *sign_e1     = NULL;
  BtorExp *sign_e2     = NULL;
  BtorExp *sign_result = NULL;
  BtorExp *add         = NULL;
  BtorExp *and1        = NULL;
  BtorExp *and2        = NULL;
  BtorExp *or1         = NULL;
  BtorExp *or2         = NULL;
  int len              = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len         = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1     = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2     = btor_slice_exp (emgr, e1, len - 1, len - 1);
  add         = btor_add_exp (emgr, e0, e1);
  sign_result = btor_slice_exp (emgr, add, len - 1, len - 1);
  and1        = btor_and_exp (emgr, sign_e1, sign_e2);
  or1         = btor_and_exp (emgr, and1, BTOR_INVERT_EXP (sign_result));
  and2 =
      btor_and_exp (emgr, BTOR_INVERT_EXP (sign_e1), BTOR_INVERT_EXP (sign_e2));
  or2    = btor_and_exp (emgr, and2, sign_result);
  result = btor_or_exp (emgr, or1, or2);
  btor_release_exp (emgr, and1);
  btor_release_exp (emgr, and2);
  btor_release_exp (emgr, or1);
  btor_release_exp (emgr, or2);
  btor_release_exp (emgr, add);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, sign_result);
  return result;
}

BtorExp *
btor_umul_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_UMUL_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL)
    result = btor_binary_exp (emgr, BTOR_UMUL_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_umulo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result    = NULL;
  BtorExp *uext_e1   = NULL;
  BtorExp *uext_e2   = NULL;
  BtorExp *umul      = NULL;
  BtorExp *slice     = NULL;
  BtorExp *and       = NULL;
  BtorExp * or       = NULL;
  BtorExp **temps_e2 = NULL;
  int i              = 0;
  int len            = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 1) return zeros_exp (emgr, 1);
  temps_e2 =
      (BtorExp **) btor_malloc (emgr->mm, sizeof (BtorExp *) * (len - 1));
  temps_e2[0] = btor_slice_exp (emgr, e1, len - 1, len - 1);
  for (i = 1; i < len - 1; i++)
  {
    slice       = btor_slice_exp (emgr, e1, len - 1 - i, len - 1 - i);
    temps_e2[i] = btor_or_exp (emgr, temps_e2[i - 1], slice);
    btor_release_exp (emgr, slice);
  }
  slice  = btor_slice_exp (emgr, e0, 1, 1);
  result = btor_and_exp (emgr, slice, temps_e2[0]);
  btor_release_exp (emgr, slice);
  for (i = 1; i < len - 1; i++)
  {
    slice = btor_slice_exp (emgr, e0, i + 1, i + 1);
    and   = btor_and_exp (emgr, slice, temps_e2[i]);
    or    = btor_or_exp (emgr, result, and);
    btor_release_exp (emgr, slice);
    btor_release_exp (emgr, and);
    btor_release_exp (emgr, result);
    result = or ;
  }
  uext_e1 = btor_uext_exp (emgr, e0, 1);
  uext_e2 = btor_uext_exp (emgr, e1, 1);
  umul    = btor_umul_exp (emgr, uext_e1, uext_e2);
  slice   = btor_slice_exp (emgr, umul, len, len);
  or      = btor_or_exp (emgr, result, slice);
  btor_release_exp (emgr, uext_e1);
  btor_release_exp (emgr, uext_e2);
  btor_release_exp (emgr, umul);
  btor_release_exp (emgr, slice);
  btor_release_exp (emgr, result);
  result = or ;
  for (i = 0; i < len - 1; i++) btor_release_exp (emgr, temps_e2[i]);
  btor_free (emgr->mm, temps_e2, sizeof (BtorExp *) * (len - 1));
  return result;
}

BtorExp *
btor_smul_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result   = NULL;
  BtorExp *sign_e1  = NULL;
  BtorExp *sign_e2  = NULL;
  BtorExp * xor     = NULL;
  BtorExp *neg_e1   = NULL;
  BtorExp *neg_e2   = NULL;
  BtorExp *cond_e1  = NULL;
  BtorExp *cond_e2  = NULL;
  BtorExp *umul     = NULL;
  BtorExp *neg_umul = NULL;
  int len           = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2 = btor_slice_exp (emgr, e1, len - 1, len - 1);
  /* xor: must result be signed? */
  xor    = btor_xor_exp (emgr, sign_e1, sign_e2);
  neg_e1 = btor_neg_exp (emgr, e0);
  neg_e2 = btor_neg_exp (emgr, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = btor_cond_exp (emgr, sign_e1, neg_e1, e0);
  cond_e2  = btor_cond_exp (emgr, sign_e2, neg_e2, e1);
  umul     = btor_umul_exp (emgr, cond_e1, cond_e2);
  neg_umul = btor_neg_exp (emgr, umul);
  /* sign result if necessary */
  result = btor_cond_exp (emgr, xor, neg_umul, umul);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, xor);
  btor_release_exp (emgr, neg_e1);
  btor_release_exp (emgr, neg_e2);
  btor_release_exp (emgr, cond_e1);
  btor_release_exp (emgr, cond_e2);
  btor_release_exp (emgr, umul);
  btor_release_exp (emgr, neg_umul);
  return result;
}

BtorExp *
btor_smulo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result          = NULL;
  BtorExp *sext_e1         = NULL;
  BtorExp *sext_e2         = NULL;
  BtorExp *sign_e1         = NULL;
  BtorExp *sign_e2         = NULL;
  BtorExp *sext_sign_e1    = NULL;
  BtorExp *sext_sign_e2    = NULL;
  BtorExp *xor_sign_e1     = NULL;
  BtorExp *xor_sign_e2     = NULL;
  BtorExp *smul            = NULL;
  BtorExp *slice           = NULL;
  BtorExp *slice_n         = NULL;
  BtorExp *slice_n_minus_1 = NULL;
  BtorExp * xor            = NULL;
  BtorExp *and             = NULL;
  BtorExp * or             = NULL;
  BtorExp **temps_e2       = NULL;
  int i                    = 0;
  int len                  = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 2)
  {
    sext_e1         = btor_sext_exp (emgr, e0, 1);
    sext_e2         = btor_sext_exp (emgr, e1, 1);
    smul            = btor_smul_exp (emgr, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (emgr, smul, len, len);
    slice_n_minus_1 = btor_slice_exp (emgr, smul, len - 1, len - 1);
    result          = btor_xor_exp (emgr, slice_n, slice_n_minus_1);
    btor_release_exp (emgr, sext_e1);
    btor_release_exp (emgr, sext_e2);
    btor_release_exp (emgr, smul);
    btor_release_exp (emgr, slice_n);
    btor_release_exp (emgr, slice_n_minus_1);
  }
  else
  {
    sign_e1      = btor_slice_exp (emgr, e0, len - 1, len - 1);
    sign_e2      = btor_slice_exp (emgr, e1, len - 1, len - 1);
    sext_sign_e1 = btor_sext_exp (emgr, sign_e1, len - 1);
    sext_sign_e2 = btor_sext_exp (emgr, sign_e2, len - 1);
    xor_sign_e1  = btor_xor_exp (emgr, e0, sext_sign_e1);
    xor_sign_e2  = btor_xor_exp (emgr, e1, sext_sign_e2);
    temps_e2 =
        (BtorExp **) btor_malloc (emgr->mm, sizeof (BtorExp *) * (len - 2));
    temps_e2[0] = btor_slice_exp (emgr, xor_sign_e2, len - 2, len - 2);
    for (i = 1; i < len - 2; i++)
    {
      slice = btor_slice_exp (emgr, xor_sign_e2, len - 2 - i, len - 2 - i);
      temps_e2[i] = btor_or_exp (emgr, temps_e2[i - 1], slice);
      btor_release_exp (emgr, slice);
    }
    slice  = btor_slice_exp (emgr, xor_sign_e1, 1, 1);
    result = btor_and_exp (emgr, slice, temps_e2[0]);
    btor_release_exp (emgr, slice);
    for (i = 1; i < len - 2; i++)
    {
      slice = btor_slice_exp (emgr, xor_sign_e1, i + 1, i + 1);
      and   = btor_and_exp (emgr, slice, temps_e2[i]);
      or    = btor_or_exp (emgr, result, and);
      btor_release_exp (emgr, slice);
      btor_release_exp (emgr, and);
      btor_release_exp (emgr, result);
      result = or ;
    }
    sext_e1         = btor_sext_exp (emgr, e0, 1);
    sext_e2         = btor_sext_exp (emgr, e1, 1);
    smul            = btor_smul_exp (emgr, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (emgr, smul, len, len);
    slice_n_minus_1 = btor_slice_exp (emgr, smul, len - 1, len - 1);
    xor             = btor_xor_exp (emgr, slice_n, slice_n_minus_1);
    or              = btor_or_exp (emgr, result, xor);
    btor_release_exp (emgr, sext_e1);
    btor_release_exp (emgr, sext_e2);
    btor_release_exp (emgr, sign_e1);
    btor_release_exp (emgr, sign_e2);
    btor_release_exp (emgr, sext_sign_e1);
    btor_release_exp (emgr, sext_sign_e2);
    btor_release_exp (emgr, xor_sign_e1);
    btor_release_exp (emgr, xor_sign_e2);
    btor_release_exp (emgr, smul);
    btor_release_exp (emgr, slice_n);
    btor_release_exp (emgr, slice_n_minus_1);
    btor_release_exp (emgr, xor);
    btor_release_exp (emgr, result);
    result = or ;
    for (i = 0; i < len - 2; i++) btor_release_exp (emgr, temps_e2[i]);
    btor_free (emgr->mm, temps_e2, sizeof (BtorExp *) * (len - 2));
  }
  return result;
}

BtorExp *
btor_ult_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_ULT_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = btor_binary_exp (emgr, BTOR_ULT_EXP, e0, e1, 1);
  return result;
}

BtorExp *
btor_slt_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result         = NULL;
  BtorExp *sign_e1        = NULL;
  BtorExp *sign_e2        = NULL;
  BtorExp *rest_e1        = NULL;
  BtorExp *rest_e2        = NULL;
  BtorExp *ult            = NULL;
  BtorExp *e1_signed_only = NULL;
  BtorExp *e1_e2_pos      = NULL;
  BtorExp *e1_e2_signed   = NULL;
  BtorExp *and1           = NULL;
  BtorExp *and2           = NULL;
  BtorExp * or            = NULL;
  int len                 = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2 = btor_slice_exp (emgr, e1, len - 1, len - 1);
  /* rest_e1: e0 without sign bit */
  rest_e1 = btor_slice_exp (emgr, e0, len - 2, 0);
  /* rest_e2: e1 without sign bit */
  rest_e2 = btor_slice_exp (emgr, e1, len - 2, 0);
  /* ult: is rest of e0 < rest of e1 ? */
  ult = btor_ult_exp (emgr, rest_e1, rest_e2);
  /* e1_signed_only: only e0 is negative */
  e1_signed_only = btor_and_exp (emgr, sign_e1, BTOR_INVERT_EXP (sign_e2));
  /* e1_e2_pos: e0 and e1 are positive */
  e1_e2_pos =
      btor_and_exp (emgr, BTOR_INVERT_EXP (sign_e1), BTOR_INVERT_EXP (sign_e2));
  /* e1_e2_signed: e0 and e1 are negative */
  e1_e2_signed = btor_and_exp (emgr, sign_e1, sign_e2);
  and1         = btor_and_exp (emgr, e1_e2_pos, ult);
  and2         = btor_and_exp (emgr, e1_e2_signed, ult);
  or           = btor_or_exp (emgr, and1, and2);
  result       = btor_or_exp (emgr, e1_signed_only, or);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, rest_e1);
  btor_release_exp (emgr, rest_e2);
  btor_release_exp (emgr, ult);
  btor_release_exp (emgr, e1_signed_only);
  btor_release_exp (emgr, e1_e2_pos);
  btor_release_exp (emgr, e1_e2_signed);
  btor_release_exp (emgr, and1);
  btor_release_exp (emgr, and2);
  btor_release_exp (emgr, or);
  return result;
}

BtorExp *
btor_ulte_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *ult    = NULL;
  BtorExp *eq     = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  ult    = btor_ult_exp (emgr, e0, e1);
  eq     = btor_eq_exp (emgr, e0, e1);
  result = btor_or_exp (emgr, ult, eq);
  btor_release_exp (emgr, ult);
  btor_release_exp (emgr, eq);
  return result;
}

BtorExp *
btor_slte_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *slt    = NULL;
  BtorExp *eq     = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  slt    = btor_slt_exp (emgr, e0, e1);
  eq     = btor_eq_exp (emgr, e0, e1);
  result = btor_or_exp (emgr, slt, eq);
  btor_release_exp (emgr, slt);
  btor_release_exp (emgr, eq);
  return result;
}

BtorExp *
btor_ugt_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return btor_ult_exp (emgr, e1, e0);
}

BtorExp *
btor_sgt_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  return btor_slt_exp (emgr, e1, e0);
}

BtorExp *
btor_ugte_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *ult    = NULL;
  BtorExp *eq     = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  ult    = btor_ult_exp (emgr, e1, e0);
  eq     = btor_eq_exp (emgr, e0, e1);
  result = btor_or_exp (emgr, ult, eq);
  btor_release_exp (emgr, ult);
  btor_release_exp (emgr, eq);
  return result;
}

BtorExp *
btor_sgte_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *slt    = NULL;
  BtorExp *eq     = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  slt    = btor_slt_exp (emgr, e1, e0);
  eq     = btor_eq_exp (emgr, e0, e1);
  result = btor_or_exp (emgr, slt, eq);
  btor_release_exp (emgr, slt);
  btor_release_exp (emgr, eq);
  return result;
}

BtorExp *
btor_sll_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_SLL_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL)
    result = btor_binary_exp (emgr, BTOR_SLL_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_srl_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_SRL_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL)
    result = btor_binary_exp (emgr, BTOR_SRL_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_sra_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result  = NULL;
  BtorExp *sign_e1 = NULL;
  BtorExp *srl1    = NULL;
  BtorExp *srl2    = NULL;
  int len          = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  srl1    = btor_srl_exp (emgr, e0, e1);
  srl2    = btor_srl_exp (emgr, BTOR_INVERT_EXP (e0), e1);
  result  = btor_cond_exp (emgr, sign_e1, BTOR_INVERT_EXP (srl2), srl1);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, srl1);
  btor_release_exp (emgr, srl2);
  return result;
}

BtorExp *
btor_rol_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *sll    = NULL;
  BtorExp *neg_e2 = NULL;
  BtorExp *srl    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  sll    = btor_sll_exp (emgr, e0, e1);
  neg_e2 = btor_neg_exp (emgr, e1);
  srl    = btor_srl_exp (emgr, e0, neg_e2);
  result = btor_or_exp (emgr, sll, srl);
  btor_release_exp (emgr, sll);
  btor_release_exp (emgr, neg_e2);
  btor_release_exp (emgr, srl);
  return result;
}

BtorExp *
btor_ror_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *srl    = NULL;
  BtorExp *neg_e2 = NULL;
  BtorExp *sll    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  srl    = btor_srl_exp (emgr, e0, e1);
  neg_e2 = btor_neg_exp (emgr, e1);
  sll    = btor_sll_exp (emgr, e0, neg_e2);
  result = btor_or_exp (emgr, srl, sll);
  btor_release_exp (emgr, srl);
  btor_release_exp (emgr, neg_e2);
  btor_release_exp (emgr, sll);
  return result;
}

BtorExp *
btor_sub_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *neg_e2 = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  neg_e2 = btor_neg_exp (emgr, e1);
  result = btor_add_exp (emgr, e0, neg_e2);
  btor_release_exp (emgr, neg_e2);
  return result;
}

BtorExp *
btor_usubo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result  = NULL;
  BtorExp *uext_e1 = NULL;
  BtorExp *uext_e2 = NULL;
  BtorExp *add1    = NULL;
  BtorExp *add2    = NULL;
  BtorExp *one     = NULL;
  int len          = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  uext_e1 = btor_uext_exp (emgr, e0, 1);
  uext_e2 = btor_uext_exp (emgr, BTOR_INVERT_EXP (e1), 1);
  assert (len < INT_MAX);
  one    = one_exp (emgr, len + 1);
  add1   = btor_add_exp (emgr, uext_e2, one);
  add2   = btor_add_exp (emgr, uext_e1, add1);
  result = BTOR_INVERT_EXP (btor_slice_exp (emgr, add2, len, len));
  btor_release_exp (emgr, uext_e1);
  btor_release_exp (emgr, uext_e2);
  btor_release_exp (emgr, add1);
  btor_release_exp (emgr, add2);
  btor_release_exp (emgr, one);
  return result;
}

BtorExp *
btor_ssubo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result      = NULL;
  BtorExp *sign_e1     = NULL;
  BtorExp *sign_e2     = NULL;
  BtorExp *sign_result = NULL;
  BtorExp *sub         = NULL;
  BtorExp *and1        = NULL;
  BtorExp *and2        = NULL;
  BtorExp *or1         = NULL;
  BtorExp *or2         = NULL;
  int len              = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len         = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1     = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2     = btor_slice_exp (emgr, e1, len - 1, len - 1);
  sub         = btor_sub_exp (emgr, e0, e1);
  sign_result = btor_slice_exp (emgr, sub, len - 1, len - 1);
  and1        = btor_and_exp (emgr, BTOR_INVERT_EXP (sign_e1), sign_e2);
  or1         = btor_and_exp (emgr, and1, sign_result);
  and2        = btor_and_exp (emgr, sign_e1, BTOR_INVERT_EXP (sign_e2));
  or2         = btor_and_exp (emgr, and2, BTOR_INVERT_EXP (sign_result));
  result      = btor_or_exp (emgr, or1, or2);
  btor_release_exp (emgr, and1);
  btor_release_exp (emgr, and2);
  btor_release_exp (emgr, or1);
  btor_release_exp (emgr, or2);
  btor_release_exp (emgr, sub);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, sign_result);
  return result;
}

BtorExp *
btor_udiv_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_UDIV_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL)
    result = btor_binary_exp (emgr, BTOR_UDIV_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_sdiv_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result   = NULL;
  BtorExp *sign_e1  = NULL;
  BtorExp *sign_e2  = NULL;
  BtorExp * xor     = NULL;
  BtorExp *neg_e1   = NULL;
  BtorExp *neg_e2   = NULL;
  BtorExp *cond_e1  = NULL;
  BtorExp *cond_e2  = NULL;
  BtorExp *udiv     = NULL;
  BtorExp *neg_udiv = NULL;
  int len           = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2 = btor_slice_exp (emgr, e1, len - 1, len - 1);
  /* xor: must result be signed? */
  xor    = btor_xor_exp (emgr, sign_e1, sign_e2);
  neg_e1 = btor_neg_exp (emgr, e0);
  neg_e2 = btor_neg_exp (emgr, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = btor_cond_exp (emgr, sign_e1, neg_e1, e0);
  cond_e2  = btor_cond_exp (emgr, sign_e2, neg_e2, e1);
  udiv     = btor_udiv_exp (emgr, cond_e1, cond_e2);
  neg_udiv = btor_neg_exp (emgr, udiv);
  /* sign result if necessary */
  result = btor_cond_exp (emgr, xor, neg_udiv, udiv);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, xor);
  btor_release_exp (emgr, neg_e1);
  btor_release_exp (emgr, neg_e2);
  btor_release_exp (emgr, cond_e1);
  btor_release_exp (emgr, cond_e2);
  btor_release_exp (emgr, udiv);
  btor_release_exp (emgr, neg_udiv);
  return result;
}

BtorExp *
btor_sdivo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result  = NULL;
  BtorExp *int_min = NULL;
  BtorExp *ones    = NULL;
  BtorExp *eq1     = NULL;
  BtorExp *eq2     = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  int_min = int_min_exp (emgr, BTOR_REAL_ADDR_EXP (e0)->len);
  ones    = ones_exp (emgr, BTOR_REAL_ADDR_EXP (e1)->len);
  eq1     = btor_eq_exp (emgr, e0, int_min);
  eq2     = btor_eq_exp (emgr, e1, ones);
  result  = btor_and_exp (emgr, eq1, eq2);
  btor_release_exp (emgr, int_min);
  btor_release_exp (emgr, ones);
  btor_release_exp (emgr, eq1);
  btor_release_exp (emgr, eq2);
  return result;
}

BtorExp *
btor_umod_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_UMOD_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL)
    result = btor_binary_exp (emgr, BTOR_UMOD_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_smod_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result   = NULL;
  BtorExp *sign_e1  = NULL;
  BtorExp *sign_e2  = NULL;
  BtorExp *neg_e1   = NULL;
  BtorExp *neg_e2   = NULL;
  BtorExp *cond_e1  = NULL;
  BtorExp *cond_e2  = NULL;
  BtorExp *umod     = NULL;
  BtorExp *neg_umod = NULL;
  int len           = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2 = btor_slice_exp (emgr, e1, len - 1, len - 1);
  neg_e1  = btor_neg_exp (emgr, e0);
  neg_e2  = btor_neg_exp (emgr, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = btor_cond_exp (emgr, sign_e1, neg_e1, e0);
  cond_e2  = btor_cond_exp (emgr, sign_e2, neg_e2, e1);
  umod     = btor_umod_exp (emgr, cond_e1, cond_e2);
  neg_umod = btor_neg_exp (emgr, umod);
  /* sign result if necessary */
  /* result is negative if e0 is negative */
  result = btor_cond_exp (emgr, sign_e1, neg_umod, umod);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, neg_e1);
  btor_release_exp (emgr, neg_e2);
  btor_release_exp (emgr, cond_e1);
  btor_release_exp (emgr, cond_e2);
  btor_release_exp (emgr, umod);
  btor_release_exp (emgr, neg_umod);
  return result;
}

BtorExp *
btor_concat_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e0)->len
          <= INT_MAX - BTOR_REAL_ADDR_EXP (e1)->len);
  len = BTOR_REAL_ADDR_EXP (e0)->len + BTOR_REAL_ADDR_EXP (e1)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_CONCAT_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL)
    result = btor_binary_exp (emgr, BTOR_CONCAT_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_read_exp (BtorExpMgr *emgr, BtorExp *e_array, BtorExp *e_index)
{
  assert (emgr != NULL);
  assert (e_array != NULL);
  assert (e_index != NULL);
  assert (!BTOR_IS_INVERTED_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (e_array->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e_index)->len > 0);
  assert (e_array->index_len == BTOR_REAL_ADDR_EXP (e_index)->len);
  return btor_binary_exp (emgr, BTOR_READ_EXP, e_array, e_index, e_array->len);
}

static BtorExp *
btor_ternary_exp (BtorExpMgr *emgr,
                  BtorExpKind kind,
                  BtorExp *e0,
                  BtorExp *e1,
                  BtorExp *e2,
                  int len)
{
  BtorExp **lookup = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  assert (len > 0);
  lookup = find_ternary_exp (emgr, kind, e0, e1, e2);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_ternary_exp (emgr, kind, e0, e1, e2);
    }
    *lookup = new_ternary_exp_node (emgr, kind, e0, e1, e2, len);
    inc_exp_ref_counter (e0);
    inc_exp_ref_counter (e1);
    inc_exp_ref_counter (e2);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
  }
  else
  {
    inc_exp_ref_counter (*lookup);
  }
  assert (!BTOR_IS_INVERTED_EXP (*lookup));
  return *lookup;
}

BtorExp *
btor_cond_exp (BtorExpMgr *emgr,
               BtorExp *e_cond,
               BtorExp *e_if,
               BtorExp *e_else)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e_cond != NULL);
  assert (e_if != NULL);
  assert (e_else != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_else)));
  assert (BTOR_REAL_ADDR_EXP (e_cond)->len == 1);
  assert (BTOR_REAL_ADDR_EXP (e_if)->len == BTOR_REAL_ADDR_EXP (e_else)->len);
  assert (BTOR_REAL_ADDR_EXP (e_if)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e_if)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_COND_EXP, e_cond, e_if, e_else, 0, 0);
  if (result == NULL)
    result = btor_ternary_exp (emgr, BTOR_COND_EXP, e_cond, e_if, e_else, len);
  return result;
}

int
btor_get_exp_len (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  return BTOR_REAL_ADDR_EXP (exp)->len;
}

int
btor_is_array_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  return BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp));
}

int
btor_get_index_exp_len (BtorExpMgr *emgr, BtorExp *e_array)
{
  assert (emgr != NULL);
  assert (e_array != NULL);
  assert (!BTOR_IS_INVERTED_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  return e_array->index_len;
}

char *
btor_get_symbol_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (exp))
          || BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  return BTOR_REAL_ADDR_EXP (exp)->symbol;
}

void
btor_dump_exp (BtorExpMgr *emgr, FILE *file, BtorExp *exp)
{
  char idbuffer[20];
  const char *name;
  BtorExpPtrStack stack;
  BtorExp *cur = NULL;
  assert (emgr != NULL);
  assert (file != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (emgr->mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    assert (cur->mark >= 0);
    assert (cur->mark <= 2);
    if (cur->mark != 2)
    {
      if (cur->mark == 0)
      {
        if (BTOR_IS_CONST_EXP (cur))
        {
          cur->mark = 2;
          fprintf (file, "%d const %d %s\n", cur->id, cur->len, cur->bits);
        }
        else if (BTOR_IS_VAR_EXP (cur))
        {
          cur->mark = 2;
          fprintf (file, "%d var %d", cur->id, cur->len);
          sprintf (idbuffer, "%d", cur->id);
          name = btor_get_symbol_exp (emgr, cur);
          if (strcmp (name, idbuffer)) fprintf (file, " %s", name);
          putc ('\n', file);
        }
        else if (BTOR_IS_ARRAY_EXP (cur))
        {
          cur->mark = 2;
          fprintf (file, "%d array %d %d\n", cur->id, cur->len, cur->index_len);
        }
        else
        {
          cur->mark = 1;
          BTOR_PUSH_STACK (emgr->mm, stack, cur);
          if (BTOR_IS_UNARY_EXP (cur))
          {
            BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
          }
          else if (BTOR_IS_BINARY_EXP (cur))
          {
            BTOR_PUSH_STACK (emgr->mm, stack, cur->e[1]);
            BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
          }
          else
          {
            assert (BTOR_IS_TERNARY_EXP (cur));
            BTOR_PUSH_STACK (emgr->mm, stack, cur->e[2]);
            BTOR_PUSH_STACK (emgr->mm, stack, cur->e[1]);
            BTOR_PUSH_STACK (emgr->mm, stack, cur->e[0]);
          }
        }
      }
      else
      {
        assert (cur->mark == 1);
        cur->mark = 2;
        fprintf (file, "%d ", cur->id);
        if (BTOR_IS_UNARY_EXP (cur))
        {
          assert (cur->kind == BTOR_SLICE_EXP);
          fprintf (file,
                   "slice %d %d %d %d\n",
                   cur->len,
                   BTOR_IS_INVERTED_EXP (cur->e[0])
                       ? -BTOR_INVERT_EXP (cur->e[0])->id
                       : cur->e[0]->id,
                   cur->upper,
                   cur->lower);
        }
        else if (BTOR_IS_BINARY_EXP (cur))
        {
          switch (cur->kind)
          {
            case BTOR_AND_EXP: fprintf (file, "and"); break;
            case BTOR_EQ_EXP: fprintf (file, "eq"); break;
            case BTOR_ADD_EXP: fprintf (file, "add"); break;
            case BTOR_UMUL_EXP: fprintf (file, "umul"); break;
            case BTOR_ULT_EXP: fprintf (file, "ult"); break;
            case BTOR_SLL_EXP: fprintf (file, "sll"); break;
            case BTOR_SRL_EXP: fprintf (file, "srl"); break;
            case BTOR_UDIV_EXP: fprintf (file, "udiv"); break;
            case BTOR_UMOD_EXP: fprintf (file, "umod"); break;
            case BTOR_CONCAT_EXP: fprintf (file, "concat"); break;
            default:
              assert (cur->kind == BTOR_READ_EXP);
              fprintf (file, "read");
              break;
          }
          fprintf (file,
                   " %d %d",
                   cur->len,
                   BTOR_IS_INVERTED_EXP (cur->e[0])
                       ? -BTOR_INVERT_EXP (cur->e[0])->id
                       : cur->e[0]->id);
          fprintf (file,
                   " %d\n",
                   BTOR_IS_INVERTED_EXP (cur->e[1])
                       ? -BTOR_INVERT_EXP (cur->e[1])->id
                       : cur->e[1]->id);
        }
        else
        {
          assert (BTOR_IS_TERNARY_EXP (cur));
          assert (cur->kind == BTOR_COND_EXP);
          fprintf (file, "cond %d", cur->len);
          fprintf (file,
                   " %d",
                   BTOR_IS_INVERTED_EXP (cur->e[0])
                       ? -BTOR_INVERT_EXP (cur->e[0])->id
                       : cur->e[0]->id);
          fprintf (file,
                   " %d",
                   BTOR_IS_INVERTED_EXP (cur->e[1])
                       ? -BTOR_INVERT_EXP (cur->e[1])->id
                       : cur->e[1]->id);
          fprintf (file,
                   " %d\n",
                   BTOR_IS_INVERTED_EXP (cur->e[2])
                       ? -BTOR_INVERT_EXP (cur->e[2])->id
                       : cur->e[2]->id);
        }
      }
    }
  }
  BTOR_RELEASE_STACK (emgr->mm, stack);
  assert (exp->id < INT_MAX);
  if (BTOR_IS_INVERTED_EXP (exp))
    fprintf (file,
             "%d root %d %d\n",
             BTOR_INVERT_EXP (exp)->id + 1,
             BTOR_INVERT_EXP (exp)->len,
             -BTOR_INVERT_EXP (exp)->id);
  else
    fprintf (file, "%d root %d %d\n", exp->id + 1, exp->len, exp->id);
  btor_mark_exp (emgr, exp, 0);
}

BtorExpMgr *
btor_new_exp_mgr (int rewrite_level,
                  int dump_trace,
                  int verbosity,
                  FILE *trace_file)
{
  BtorMemMgr *mm   = btor_new_mem_mgr ();
  BtorExpMgr *emgr = NULL;
  assert (mm != NULL);
  assert (sizeof (int) == 4);
  assert (rewrite_level >= 0);
  assert (rewrite_level <= 2);
  assert (verbosity >= -1);
  emgr     = btor_malloc (mm, sizeof (BtorExpMgr));
  emgr->mm = mm;
  BTOR_INIT_EXP_UNIQUE_TABLE (mm, emgr->table);
  BTOR_INIT_STACK (emgr->assigned_exps);
  BTOR_INIT_STACK (emgr->vars);
  BTOR_INIT_STACK (emgr->arrays);
  emgr->avmgr         = btor_new_aigvec_mgr (emgr->mm, verbosity);
  emgr->id            = 1;
  emgr->rewrite_level = rewrite_level;
  emgr->dump_trace    = dump_trace;
  emgr->verbosity     = verbosity;
  emgr->read_enc      = BTOR_SAT_SOLVER_READ_ENC;
  emgr->trace_file    = trace_file;
  return emgr;
}

void
btor_delete_exp_mgr (BtorExpMgr *emgr)
{
  BtorExp **cur              = NULL;
  BtorReadObj *obj           = NULL;
  BtorReadObjPtrStack *stack = NULL;
  BtorMemMgr *mm             = NULL;
  assert (emgr != NULL);
  mm = emgr->mm;
  for (cur = emgr->arrays.start; cur != emgr->arrays.top; cur++)
  {
    stack = (*cur)->read_constraint;
    while (!BTOR_EMPTY_STACK (*stack))
    {
      obj = BTOR_POP_STACK (*stack);
      delete_read_obj (emgr, obj);
    }
  }
  for (cur = emgr->vars.start; cur != emgr->vars.top; cur++)
    delete_exp_node (emgr, *cur);
  for (cur = emgr->arrays.start; cur != emgr->arrays.top; cur++)
    delete_exp_node (emgr, *cur);
  assert (emgr->table.num_elements == 0);
  BTOR_RELEASE_EXP_UNIQUE_TABLE (mm, emgr->table);
  BTOR_RELEASE_STACK (emgr->mm, emgr->assigned_exps);
  BTOR_RELEASE_STACK (emgr->mm, emgr->vars);
  BTOR_RELEASE_STACK (emgr->mm, emgr->arrays);
  btor_delete_aigvec_mgr (emgr->avmgr);
  btor_free (emgr->mm, emgr, sizeof (BtorExpMgr));
  btor_delete_mem_mgr (mm);
}

void
btor_set_read_enc_exp_mgr (BtorExpMgr *emgr, BtorReadEnc read_enc)
{
  assert (emgr != NULL);
  emgr->read_enc = read_enc;
}

BtorMemMgr *
btor_get_mem_mgr_exp_mgr (BtorExpMgr *emgr)
{
  assert (emgr != NULL);
  return emgr->mm;
}

BtorAIGVecMgr *
btor_get_aigvec_mgr_exp_mgr (BtorExpMgr *emgr)
{
  assert (emgr != NULL);
  return emgr->avmgr;
}

BtorAIG *
btor_exp_to_aig (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExpPtrStack exp_stack;
  BtorExp *cur         = NULL;
  BtorAIG *result      = NULL;
  BtorAIGVec *av0      = NULL;
  BtorAIGVec *av1      = NULL;
  BtorAIGVec *av2      = NULL;
  BtorAIGVecMgr *avmgr = NULL;
  BtorAIGMgr *amgr     = NULL;
  BtorMemMgr *mm       = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);
  if (emgr->verbosity > 1)
    print_verbose_msg ("transforming expression into AIG\n");
  mm    = emgr->mm;
  avmgr = emgr->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  BTOR_INIT_STACK (exp_stack);
  BTOR_PUSH_STACK (mm, exp_stack, exp);
  while (!BTOR_EMPTY_STACK (exp_stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (exp_stack));
    assert (cur->mark >= 0);
    assert (cur->mark <= 1);
    assert (!BTOR_IS_ARRAY_EXP (cur));
    if (cur->av == NULL)
    {
      if (cur->mark == 0)
      {
        if (BTOR_IS_CONST_EXP (cur))
        {
          cur->av = btor_const_aigvec (avmgr, cur->bits);
        }
        else if (BTOR_IS_VAR_EXP (cur))
        {
          cur->av = btor_var_aigvec (avmgr, cur->len);
        }
        else
        {
          cur->mark = 1;
          BTOR_PUSH_STACK (mm, exp_stack, cur);
          if (cur->kind == BTOR_READ_EXP)
          {
            /* push index on the stack */
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
          }
          else if (BTOR_IS_UNARY_EXP (cur))
          {
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
          }
          else if (BTOR_IS_BINARY_EXP (cur))
          {
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
          }
          else
          {
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[2]);
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
          }
        }
      }
      else
      {
        assert (cur->mark == 1);
        if (cur->kind == BTOR_READ_EXP)
        {
          /* generate new AIGs for read */
          cur->av = btor_var_aigvec (avmgr, cur->len);
          /* cur->e[0] is array */
          register_read (emgr, cur->e[0], cur, cur->e[1]);
        }
        else if (BTOR_IS_UNARY_EXP (cur))
        {
          assert (cur->kind == BTOR_SLICE_EXP);
          if (BTOR_IS_INVERTED_EXP (cur->e[0]))
            av0 = btor_not_aigvec (avmgr, BTOR_REAL_ADDR_EXP (cur->e[0])->av);
          else
            av0 = btor_copy_aigvec (avmgr, cur->e[0]->av);
          cur->av = btor_slice_aigvec (avmgr, av0, cur->upper, cur->lower);
          btor_release_delete_aigvec (avmgr, av0);
        }
        else if (BTOR_IS_BINARY_EXP (cur))
        {
          if (BTOR_IS_INVERTED_EXP (cur->e[0]))
            av0 = btor_not_aigvec (avmgr, BTOR_REAL_ADDR_EXP (cur->e[0])->av);
          else
            av0 = btor_copy_aigvec (avmgr, cur->e[0]->av);
          if (BTOR_IS_INVERTED_EXP (cur->e[1]))
            av1 = btor_not_aigvec (avmgr, BTOR_REAL_ADDR_EXP (cur->e[1])->av);
          else
            av1 = btor_copy_aigvec (avmgr, cur->e[1]->av);
          switch (cur->kind)
          {
            case BTOR_AND_EXP:
              cur->av = btor_and_aigvec (avmgr, av0, av1);
              break;
            case BTOR_EQ_EXP: cur->av = btor_eq_aigvec (avmgr, av0, av1); break;
            case BTOR_ADD_EXP:
              cur->av = btor_add_aigvec (avmgr, av0, av1);
              break;
            case BTOR_UMUL_EXP:
              cur->av = btor_umul_aigvec (avmgr, av0, av1);
              break;
            case BTOR_ULT_EXP:
              cur->av = btor_ult_aigvec (avmgr, av0, av1);
              break;
            case BTOR_SLL_EXP:
              cur->av = btor_sll_aigvec (avmgr, av0, av1);
              break;
            case BTOR_SRL_EXP:
              cur->av = btor_srl_aigvec (avmgr, av0, av1);
              break;
            case BTOR_UDIV_EXP:
              cur->av = btor_udiv_aigvec (avmgr, av0, av1);
              break;
            case BTOR_UMOD_EXP:
              cur->av = btor_umod_aigvec (avmgr, av0, av1);
              break;
            default:
              assert (cur->kind == BTOR_CONCAT_EXP);
              cur->av = btor_concat_aigvec (avmgr, av0, av1);
              break;
          }
          btor_release_delete_aigvec (avmgr, av0);
          btor_release_delete_aigvec (avmgr, av1);
        }
        else
        {
          assert (BTOR_IS_TERNARY_EXP (cur));
          assert (cur->kind == BTOR_COND_EXP);
          if (BTOR_IS_INVERTED_EXP (cur->e[0]))
            av0 = btor_not_aigvec (avmgr, BTOR_REAL_ADDR_EXP (cur->e[0])->av);
          else
            av0 = btor_copy_aigvec (avmgr, cur->e[0]->av);
          if (BTOR_IS_INVERTED_EXP (cur->e[1]))
            av1 = btor_not_aigvec (avmgr, BTOR_REAL_ADDR_EXP (cur->e[1])->av);
          else
            av1 = btor_copy_aigvec (avmgr, cur->e[1]->av);
          if (BTOR_IS_INVERTED_EXP (cur->e[2]))
            av2 = btor_not_aigvec (avmgr, BTOR_REAL_ADDR_EXP (cur->e[2])->av);
          else
            av2 = btor_copy_aigvec (avmgr, cur->e[2]->av);
          cur->av = btor_cond_aigvec (avmgr, av0, av1, av2);
          btor_release_delete_aigvec (avmgr, av2);
          btor_release_delete_aigvec (avmgr, av1);
          btor_release_delete_aigvec (avmgr, av0);
        }
      }
    }
  }
  assert (BTOR_REAL_ADDR_EXP (exp)->av->len == 1);
  if (BTOR_IS_INVERTED_EXP (exp))
    result = btor_not_aig (amgr, BTOR_REAL_ADDR_EXP (exp)->av->aigs[0]);
  else
    result = btor_copy_aig (amgr, exp->av->aigs[0]);
  BTOR_RELEASE_STACK (mm, exp_stack);
  btor_mark_exp (emgr, exp, 0);
  return result;
}

static void
free_current_assignments (BtorExpMgr *emgr)
{
  BtorExp *cur = NULL;
  assert (emgr != NULL);
  while (!BTOR_EMPTY_STACK (emgr->assigned_exps))
  {
    cur = BTOR_POP_STACK (emgr->assigned_exps);
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_VAR_EXP (cur));
    assert (cur->assignment != NULL);
    btor_free (emgr->mm,
               cur->assignment,
               sizeof (char *) * (strlen (cur->assignment) + 1));
    cur->assignment = NULL;
  }
  BTOR_RESET_STACK (emgr->assigned_exps);
}

void
btor_exp_to_sat (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorAIG *aig     = NULL;
  BtorAIGMgr *amgr = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);
  free_current_assignments (emgr);
  amgr = btor_get_aig_mgr_aigvec_mgr (emgr->avmgr);
  aig  = btor_exp_to_aig (emgr, exp);
  if (!BTOR_IS_CONST_AIG (aig)) btor_aig_to_sat (amgr, aig);
  btor_release_aig (amgr, aig);
}

static int
compare_read_obj_sort_obj (const void *sobj1, const void *sobj2)
{
  BtorExp *index1  = NULL;
  BtorExp *index2  = NULL;
  BtorAIGVec *av1  = NULL;
  BtorAIGVec *av2  = NULL;
  BtorExpMgr *emgr = NULL;
  BtorAIGMgr *amgr = NULL;
  int val1         = 0;
  int val2         = 0;
  int len          = 0;
  int i            = 0;
  assert (sobj1 != NULL);
  assert (sobj2 != NULL);
  emgr   = ((BtorReadObjSortObj *) sobj1)->emgr;
  amgr   = btor_get_aig_mgr_aigvec_mgr (emgr->avmgr);
  index1 = ((BtorReadObjSortObj *) sobj1)->obj->index;
  index2 = ((BtorReadObjSortObj *) sobj2)->obj->index;
  assert (BTOR_REAL_ADDR_EXP (index1)->len == BTOR_REAL_ADDR_EXP (index2)->len);
  av1 = BTOR_REAL_ADDR_EXP (index1)->av;
  av2 = BTOR_REAL_ADDR_EXP (index2)->av;
  assert (av1->len == av2->len);
  len = av1->len;
  for (i = 0; i < len; i++)
  {
    val1 = btor_get_assignment_aig (amgr, av1->aigs[i]);
    assert (val1 >= -1);
    assert (val1 <= 1);
    if (val1 == 0) val1 = -1;
    val2 = btor_get_assignment_aig (amgr, av2->aigs[i]);
    assert (val1 >= -1);
    assert (val1 <= 1);
    if (val2 == 0) val2 = -1;
    if (val1 < val2) return -1;
    if (val2 < val1) return 1;
  }
  return 0;
}

static int
resolve_read_conflicts (BtorExpMgr *emgr)
{
  BtorExp **cur_exp          = NULL;
  BtorReadObjPtrStack *stack = NULL;
  BtorReadObj **cur_obj      = NULL;
  BtorReadObjSortObj **array = NULL;
  int counter                = 0;
  int len                    = 0;
  int found_conflict         = 0;
  /* iterate over all arrays */
  for (cur_exp = emgr->arrays.start; cur_exp != emgr->arrays.top; cur_exp++)
  {
    stack = (*cur_exp)->read_constraint;
    len   = BTOR_COUNT_STACK (*stack);
    if (len > 0)
    {
      /* copy pointers to read objects and sort array */
      array = (BtorReadObjSortObj **) btor_malloc (
          emgr->mm, sizeof (BtorReadObjSortObj *) * len);
      counter = 0;
      for (cur_obj = (*stack).start; cur_obj != (*stack).top; cur_obj++)
        array[counter++] = new_read_obj_sort_obj (emgr, *cur_obj);
      assert (counter == len);
      qsort (
          array, len, sizeof (BtorReadObjSortObj *), compare_read_obj_sort_obj);
      for (counter = 0; counter < len; counter++)
        delete_read_obj_sort_obj (emgr, array[counter]);
    }
  }
  return found_conflict;
}

int
btor_sat_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  int result       = 0;
  BtorAIG *aig     = NULL;
  BtorAIGMgr *amgr = NULL;
  BtorSATMgr *smgr = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);
  free_current_assignments (emgr);
  amgr = btor_get_aig_mgr_aigvec_mgr (emgr->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  aig  = btor_exp_to_aig (emgr, exp);
  if (aig == BTOR_AIG_FALSE) return BTOR_UNSAT;
  if (aig != BTOR_AIG_TRUE) btor_aig_to_sat (amgr, aig);
  result = btor_sat_sat (smgr, INT_MAX);
  btor_release_aig (amgr, aig);
  return result;
}

char *
btor_get_assignment_var_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  char *assignment = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));
  assert (!BTOR_IS_ARRAY_EXP (exp));
  assert (BTOR_IS_VAR_EXP (exp));
  if (exp->av == NULL) return NULL;
  if (exp->assignment != NULL) return exp->assignment;
  assignment      = btor_get_assignment_aigvec (emgr->avmgr, exp->av);
  exp->assignment = assignment;
  BTOR_PUSH_STACK (emgr->mm, emgr->assigned_exps, exp);
  return assignment;
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/

#include "btormc.h"
#include "btorstack.h"

typedef enum BtorKindNodeMC
{
  BTOR_MC_INPUT_NODE = 1,
  BTOR_MC_LATCH_NODE = 2,
} BtorMCType;

typedef struct BtorNodeMC BtorNodeMC;

struct BtorMCN
{
  int id;
  BtorKindNodeMC kind;
  BtorNode* node;
  BtorNodePtrStack copies;
};

struct BtorMC
{
};

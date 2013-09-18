#include "AigUtils.hpp"
#include "aig/saig/saig.h"

#include "avy/Util/AvyAssert.hpp"

using namespace abc;
namespace avy
{

  /** 
   * Duplicate pCombMan but keep only one specified output
   */
  Aig_Man_t *Aig_ManDupSinglePo (Aig_Man_t *pCombMan, int nPo)
  {
    AVY_ASSERT ( Aig_ManRegNum (pCombMan) == 0 );
    AVY_ASSERT ( Aig_ManCoNum (pCombMan) >= nPo );

    // create the new manager
    Aig_Man_t *pNew = Aig_ManStart( Aig_ManObjNumMax(pCombMan));
    pNew->pName = Abc_UtilStrsav( pCombMan->pName );
    pNew->pSpec = Abc_UtilStrsav( pCombMan->pSpec );

    // -- move nodes
    Aig_ManConst1(pCombMan)->pData = Aig_ManConst1(pNew);
    
    // -- inputs
    int i;
    Aig_Obj_t * pObj;
    Aig_ManForEachCi( pCombMan, pObj, i ) pObj->pData = Aig_ObjCreateCi( pNew );

    // duplicate internal nodes
    Aig_ManForEachNode( pCombMan, pObj, i )
      pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );

    AVY_ASSERT (Aig_ObjChild0Copy (Aig_ManCo(pCombMan, nPo)) != NULL);
    Aig_ObjCreateCo (pNew, Aig_ObjChild0Copy (Aig_ManCo(pCombMan, nPo)));

    Aig_ManCleanData (pCombMan);
    
    Aig_ManCleanup( pNew );
  }
  
  
  /** 
      Replace or create PO of pSeqMan with pCombMan. 
      CI of pCombMan are mapped to Registers of pSeqMan.
   */
  Aig_Man_t *Aig_ManReplacePo (Aig_Man_t *pSeqMan, Aig_Man_t *pCombMan, bool fCompl=false)
  {
    // Only one property output.
    AVY_ASSERT(Saig_ManPoNum(pSeqMan) - Saig_ManConstrNum(pSeqMan) == 1 
               && "pSeqMan has more than one property output");

    AVY_ASSERT ( Aig_ManRegNum(pSeqMan) > 0 && "pSeqMan is not sequential");
    AVY_ASSERT ( Aig_ManRegNum (pCombMan) == 0 );
    AVY_ASSERT ( Aig_ManCoNum (pCombMan) == 1 );
    AVY_ASSERT(Aig_ManCiNum(pCombMan) == Saig_ManRegNum(pSeqMan));
    AVY_ASSERT (Saig_ManConstrNum(pSeqMan) == 0);
    
    Aig_ManCleanData (pSeqMan);
    Aig_ManCleanData (pCombMan);
    
    // create the new manager
    Aig_Man_t *pNew = Aig_ManStart( Aig_ManObjNumMax(pSeqMan) + Aig_ManObjNumMax (pCombMan));
    pNew->pName = Abc_UtilStrsav( pSeqMan->pName );
    pNew->pSpec = Abc_UtilStrsav( pSeqMan->pSpec );

    // -- move pSeqMan
    Aig_ManConst1(pSeqMan)->pData = Aig_ManConst1(pNew);

    // -- inputs
    int i;
    Aig_Obj_t * pObj;
    Aig_ManForEachCi( pSeqMan, pObj, i ) pObj->pData = Aig_ObjCreateCi( pNew );

    // set registers
    pNew->nTruePis = pSeqMan->nTruePis;
    pNew->nTruePos = Saig_ManConstrNum(pSeqMan) + 1;
    pNew->nRegs    = pSeqMan->nRegs;

    // duplicate internal nodes
    Aig_ManForEachNode( pSeqMan, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );

    // -- move pCombMan
    Aig_ManConst1(pCombMan)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachLo(pSeqMan, pObj, i)
      {
        AVY_ASSERT (Aig_ManCiNum (pCombMan) > i);  // XXX factor outside the loop?
        // -- map CI in the Miter to where Lo of pSeqMan is mapped in pNew
        Aig_ManCi(pCombMan, i)->pData = pObj->pData;
      }

    // -- sanity check. No missing CI
    Aig_ManForEachCi(pCombMan, pObj, i) AVY_ASSERT (pObj->pData != NULL);

    // -- copy nodes
    Aig_ManForEachNode(pCombMan, pObj, i)
      {
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        AVY_ASSERT (pObj->pData != NULL);
      }

    // -- po
    AVY_ASSERT (Aig_ObjChild0Copy (Aig_ManCo(pCombMan, 0)) != NULL);
    Aig_ObjCreateCo (pNew, Aig_NotCond (Aig_ObjChild0Copy (Aig_ManCo(pCombMan, 0)), fCompl));

    // -- wire circuit latches
    Saig_ManForEachLi( pSeqMan, pObj, i ) 
      Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );

    Aig_ManCleanData (pSeqMan);
    Aig_ManCleanData (pCombMan);
    
    Aig_ManCleanup( pNew );
    return pNew;
  }
  
}

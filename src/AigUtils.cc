#include "AigUtils.hpp"
#include "aig/saig/saig.h"
#include "aig/gia/giaAig.h"

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

    return pNew;
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

  Aig_Man_t *Aig_ManGiaDup (Aig_Man_t *pAig)
  {
    Gia_Man_t *pGia = Gia_ManFromAigSimple (pAig);
    return Gia_ManToAigSimple (pGia);
  }
  
  Aig_Man_t *Aig_ManRebuild (Aig_Man_t **ppAig)
  {
    Aig_Man_t *pRes = Aig_ManGiaDup (*ppAig);
    Aig_ManStop (*ppAig);
    *ppAig = pRes;
    return pRes;
  }

  bool Aig_ObjDbgCompare (Aig_Obj_t *pObj1, Aig_Obj_t *pObj2)
  {
    AVY_ASSERT (Aig_IsComplement (pObj1) == Aig_IsComplement (pObj2));
    pObj1 = Aig_Regular (pObj1);
    pObj2 = Aig_Regular (pObj2);
    if (Aig_ObjId (pObj1) != Aig_ObjId (pObj2))
      {
        std::cerr  << "Left: " << Aig_ObjId (pObj1) 
                   << " | Right: " << Aig_ObjId (pObj2) << "\n";
        AVY_UNREACHABLE ();
      }
    
    return true;
  }
  
  bool Aig_ManDbgCompare (abc::Aig_Man_t *pAig1, abc::Aig_Man_t *pAig2)
  {
    AVY_ASSERT (Aig_ManCiNum (pAig1) == Aig_ManCiNum (pAig2));
    AVY_ASSERT (Aig_ManCoNum (pAig1) == Aig_ManCoNum (pAig2));
    AVY_ASSERT (Aig_ManBufNum (pAig1) == Aig_ManBufNum (pAig2));
    AVY_ASSERT (Aig_ManAndNum (pAig1) == Aig_ManAndNum (pAig2));
    AVY_ASSERT (Aig_ManNodeNum (pAig1) == Aig_ManNodeNum (pAig2));

    Aig_Obj_t *pObj;
    int i;
    Aig_ManForEachCi (pAig1, pObj, i)
      Aig_ObjDbgCompare (pObj, Aig_ManCi (pAig2, i));
    Aig_ManForEachCo (pAig1, pObj, i)
      Aig_ObjDbgCompare (pObj, Aig_ManCo (pAig2, i));
    return true;
  }
  

  
  
}

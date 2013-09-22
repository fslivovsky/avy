#include "aig/saig/saig.h"
#include "aig/gia/giaAig.h"
#include "proof/dch/dch.h"

#include "AigUtils.h"
#include "avy/Util/AvyAssert.h"

using namespace abc;
namespace avy
{

  /** 
   * Duplicate p but keep only one specified output , or none if nPo is -1
   */
  Aig_Man_t *Aig_ManDupSinglePo (Aig_Man_t *p, int nPo, bool fKeepRegs)
  {
    AVY_ASSERT ( fKeepRegs == false || Aig_ManRegNum (p) > 0 );
    AVY_ASSERT ( nPo < 0 || Aig_ManCoNum (p) >= nPo );

    // create the new manager
    Aig_Man_t *pNew = Aig_ManStart( Aig_ManObjNumMax(p));
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nTruePis = p->nTruePis;
    if (nPo < 0 )
      pNew->nTruePos = Saig_ManConstrNum (p);
    else
      pNew->nTruePos = Saig_ManConstrNum (p) + 1;
    if (fKeepRegs)
      pNew->nRegs = p->nRegs;
    else
      pNew->nRegs = 0;
    

    // -- move nodes
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    
    // -- inputs
    int i;
    Aig_Obj_t * pObj;
    Aig_ManForEachCi( p, pObj, i ) pObj->pData = Aig_ObjCreateCi( pNew );

    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
      pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), 
                             Aig_ObjChild1Copy(pObj) );

    // create constraint outputs
    Saig_ManForEachPo( p, pObj, i )
      {
        if ( i < Saig_ManPoNum(p)-Saig_ManConstrNum(p) )
          continue;
        Aig_ObjCreateCo( pNew, Aig_Not( Aig_ObjChild0Copy(pObj) ) );
      }

    if (fKeepRegs)
      {
        // -- registers
        Saig_ManForEachLi( p, pObj, i )
          Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
      }
    
        
    if (nPo >= 0)
      {
        AVY_ASSERT (Aig_ObjChild0Copy (Aig_ManCo(p, nPo)) != NULL);
        Aig_ObjCreateCo (pNew, Aig_ObjChild0Copy (Aig_ManCo(p, nPo)));
      }

    Aig_ManCleanData (p);
    Aig_ManCleanup( pNew );

    return pNew;
  }
  
  
  /** 
      Replace or create PO of pSeqMan using pCombMan. 
      CI of pCombMan are mapped to Registers of pSeqMan.
   */
  Aig_Man_t *Aig_ManReplacePo (Aig_Man_t *pSeqMan, Aig_Man_t *pCombMan, 
                               bool fCompl=false)
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
  

  Aig_Man_t *Aig_ManSimplifyComb (Aig_Man_t *p)
  {
    Dch_Pars_t pars;
    Dch_ManSetDefaultParams(&pars);
    pars.nWords = 16;
    Gia_Man_t* pGia = Gia_ManFromAigSimple(p);
    Gia_Man_t *pSynGia = Gia_ManFraigSweep(pGia, (void*)(&pars));
    Gia_ManStop(pGia);
    Aig_Man_t* pSyn = Gia_ManToAigSimple(pSynGia);
    Gia_ManStop(pSynGia);
    return pSyn;
  }

  Aig_Man_t *Aig_AddResetPi (Aig_Man_t *p)
  {
    // Only support single property for now.
    AVY_ASSERT(p->nTruePos == 1 && "Assuming single PO");
    
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    AVY_ASSERT ( Aig_ManRegNum(p) > 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nTruePis = p->nTruePis + 1;
    pNew->nTruePos = p->nTruePos;
    pNew->nRegs    = p->nRegs;
    pNew->nConstrs = Saig_ManConstrNum(p);

    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_Obj_t* pResetPi = Aig_ObjCreateCi (pNew);
    Aig_ManForEachCi( p, pObj, i )
      pObj->pData = Aig_ObjCreateCi( pNew );

    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
      pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), 
                             Aig_ObjChild1Copy(pObj) );

    Aig_Obj_t *pLi, *pLo;
    Saig_ManForEachLiLo( p, pLi, pLo, i )
      {
        Aig_Obj_t* pTmp = Aig_And(pNew, Aig_ObjChild0Copy(pLi), 
                                  Aig_Not(pResetPi));
        
        Aig_Regular(pLi->pFanin0)->pData = pTmp;
        // XXX This changes the input AIG. Seems like a bad thing to do!
        // XXX Instead, if Aig_ObjFanin0C(pLi) then negate pTmp and drop regular.
        pLi->pFanin0 = Aig_Regular(pLi->pFanin0);
      }

    // -- re-create the single PO
    pObj = Aig_ManCo(p, 0 );
    Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj) );

    // create constraint outputs
    Saig_ManForEachPo( p, pObj, i )
      {
        if ( i < Saig_ManPoNum(p)-Saig_ManConstrNum(p) )
          continue;
        Aig_ObjCreateCo( pNew, Aig_Not( Aig_ObjChild0Copy(pObj) ) );
      }

    Saig_ManForEachLi( p, pObj, i )
      Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );

    Aig_ManCleanup( pNew );
    return pNew;
  }

  Aig_Man_t *Aig_CreateAllZero (unsigned nPiNum)
  {
    int i;
    AVY_ASSERT (nPiNum > 0 );
    Aig_Obj_t ** ppInputs = ABC_ALLOC( Aig_Obj_t *, nPiNum );
    Aig_Man_t *p = Aig_ManStart( nPiNum );
    for ( i = 0; i < nPiNum; i++ ) ppInputs[i] = Aig_Not( Aig_ObjCreateCi(p) );
    Aig_Obj_t *pRes = Aig_Multi( p, ppInputs, nPiNum, AIG_OBJ_AND );
    Aig_ObjCreateCo(p, pRes );
    ABC_FREE( ppInputs );
    return p;
  }
  
  
}

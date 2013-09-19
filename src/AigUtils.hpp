#ifndef _AIGUTILS_H_
#define _AIGUTILS_H_

#include "aig/aig/aig.h"

namespace avy
{
  abc::Aig_Man_t *Aig_ManReplacePo (abc::Aig_Man_t *pSeqMan, 
                                    abc::Aig_Man_t *pCombMan, bool fComp);
  abc::Aig_Man_t *Aig_ManDupSinglePo (abc::Aig_Man_t *pCombMan, int nPo);

  /** 
   * Duplicate an Aig via Gia 
   */
  abc::Aig_Man_t *Aig_ManGiaDup (abc::Aig_Man_t *pAig);
  
  /** 
   * Rebuild an Aig via Gia and deallocate the old one
   */
  abc::Aig_Man_t *Aig_ManRebuild (abc::Aig_Man_t **ppAig);

  bool Aig_ObjDbgCompare (abc::Aig_Obj_t *pObj1, abc::Aig_Obj_t *pObj2);
  /**
   * Structurally compare two Aig for debugging
   */
  bool Aig_ManDbgCompare (abc::Aig_Man_t *pAig1, abc::Aig_Man_t *pAig2);
}



#endif /* _AIGUTILS_H_ */

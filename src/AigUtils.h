#ifndef _AIGUTILS_H_
#define _AIGUTILS_H_

#include "aig/aig/aig.h"

#include "boost/shared_ptr.hpp"

namespace avy
{


  typedef boost::shared_ptr<abc::Aig_Man_t> AigManPtr;
  
  namespace 
  { struct aig_deleter 
    { void operator() (abc::Aig_Man_t* p) { if (p) abc::Aig_ManStop (p); } }; }
  
  inline AigManPtr aigPtr (abc::Aig_Man_t *p) 
  { return AigManPtr (p, aig_deleter ());}

  inline AigManPtr newAigPtr (int nNodesMax) 
  { return aigPtr (abc::Aig_ManStart (nNodesMax)); }
  

  abc::Aig_Man_t *Aig_ManReplacePo (abc::Aig_Man_t *pSeqMan, 
                                    abc::Aig_Man_t *pCombMan, bool fComp);
  /** 
   * Duplicate an AIG but
   * keep only single po nPo 
   * or no po if nPo is -1
   * remove registers unless fKeepRegs is true
   */
  abc::Aig_Man_t *Aig_ManDupSinglePo (abc::Aig_Man_t *p, int nPo, 
                                      bool fKeepRegs=true);
  
  inline abc::Aig_Man_t *Aig_ManDupNoPo (abc::Aig_Man_t *p)
  { return Aig_ManDupSinglePo (p, -1, true); }
  

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

  /**
   * Generic simplification
   */
  abc::Aig_Man_t *Aig_ManSimplifyComb (abc::Aig_Man_t *p);
  

  /**
   * Insert a reset PI, called r.
   * When r is true, the registers are reset to 0
   */
  abc::Aig_Man_t *Aig_AddResetPi (abc::Aig_Man_t *p);

  /**
   * Insert a stuttering Pi called r.
   * When r is true, the registers do not change
   */
  abc::Aig_Man_t *Aig_AddStutterPi (abc::Aig_Man_t *p);

  /**
   * Duplicate and stutter the unique first Po
   * stick-on-error
   */
  abc::Aig_Man_t *Aig_AddStutterPo (abc::Aig_Man_t *p);

  /**
   * Create an AIG with PO = AND (!PI_0, ..., !PI_N)
   */
  abc::Aig_Man_t *Aig_CreateAllZero (unsigned nPiNum);
 
}



#endif /* _AIGUTILS_H_ */

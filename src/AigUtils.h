#ifndef _AIGUTILS_H_
#define _AIGUTILS_H_

#include "aig/aig/aig.h"

#include "boost/shared_ptr.hpp"

namespace avy
{


  typedef boost::shared_ptr<ABC_NAMESPACE::Aig_Man_t> AigManPtr;
  
  namespace 
  { struct aig_deleter 
    { void operator() (ABC_NAMESPACE::Aig_Man_t* p) { if (p) ABC_NAMESPACE::Aig_ManStop (p); } }; }
  
  inline AigManPtr aigPtr (ABC_NAMESPACE::Aig_Man_t *p)
  { return AigManPtr (p, aig_deleter ());}

  inline AigManPtr newAigPtr (int nNodesMax) 
  { return aigPtr (ABC_NAMESPACE::Aig_ManStart (nNodesMax)); }
  

  ABC_NAMESPACE::Aig_Man_t *Aig_ManReplacePo (ABC_NAMESPACE::Aig_Man_t *pSeqMan,
                                    ABC_NAMESPACE::Aig_Man_t *pCombMan, bool fComp);
  /** 
   * Duplicate an AIG but
   * keep only single po nPo 
   * or no po if nPo is -1
   * remove registers unless fKeepRegs is true
   */
  ABC_NAMESPACE::Aig_Man_t *Aig_ManDupSinglePo (ABC_NAMESPACE::Aig_Man_t *p, int nPo,
                                      bool fKeepRegs=true);
  
  inline ABC_NAMESPACE::Aig_Man_t *Aig_ManDupNoPo (ABC_NAMESPACE::Aig_Man_t *p)
  { return Aig_ManDupSinglePo (p, -1, true); }
  

  /** 
   * Duplicate an Aig via Gia 
   */
  ABC_NAMESPACE::Aig_Man_t *Aig_ManGiaDup (ABC_NAMESPACE::Aig_Man_t *pAig);
  
  /** 
   * Rebuild an Aig via Gia and deallocate the old one
   */
  ABC_NAMESPACE::Aig_Man_t *Aig_ManRebuild (ABC_NAMESPACE::Aig_Man_t **ppAig);

  bool Aig_ObjDbgCompare (ABC_NAMESPACE::Aig_Obj_t *pObj1, ABC_NAMESPACE::Aig_Obj_t *pObj2);
  /**
   * Structurally compare two Aig for debugging
   */
  bool Aig_ManDbgCompare (ABC_NAMESPACE::Aig_Man_t *pAig1, ABC_NAMESPACE::Aig_Man_t *pAig2);

  /**
   * Generic simplification
   */
  ABC_NAMESPACE::Aig_Man_t *Aig_ManSimplifyComb (ABC_NAMESPACE::Aig_Man_t *p);
  

  /**
   * Insert a reset PI, called r.
   * When r is true, the registers are reset to 0
   */
  ABC_NAMESPACE::Aig_Man_t *Aig_AddResetPi (ABC_NAMESPACE::Aig_Man_t *p);

  /**
   * Insert a stuttering Pi called r.
   * When r is true, the registers do not change
   */
  ABC_NAMESPACE::Aig_Man_t *Aig_AddStutterPi (ABC_NAMESPACE::Aig_Man_t *p);

  /**
   * Duplicate and stutter the unique first Po
   * stick-on-error
   */
  ABC_NAMESPACE::Aig_Man_t *Aig_AddStutterPo (ABC_NAMESPACE::Aig_Man_t *p);

  /**
   * Create an AIG with PO = AND (!PI_0, ..., !PI_N)
   */
  ABC_NAMESPACE::Aig_Man_t *Aig_CreateAllZero (unsigned nPiNum);
 
}



#endif /* _AIGUTILS_H_ */

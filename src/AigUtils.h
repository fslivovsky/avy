#ifndef _AIGUTILS_H_
#define _AIGUTILS_H_

#include "avy/AvyAbc.h"

#include "aig/aig/aig.h"
#include "boost/shared_ptr.hpp"

namespace avy
{
  using namespace avy::abc;
  
  typedef boost::shared_ptr<Aig_Man_t> AigManPtr;
  
  namespace 
  { struct aig_deleter 
    { void operator() (Aig_Man_t* p) { if (p) Aig_ManStop (p); } }; }
  
  inline AigManPtr aigPtr (Aig_Man_t *p)
  { return AigManPtr (p, aig_deleter ());}

  inline AigManPtr newAigPtr (int nNodesMax) 
  { return aigPtr (Aig_ManStart (nNodesMax)); }
  

  Aig_Man_t *Aig_ManReplacePo (Aig_Man_t *pSeqMan,
                                    Aig_Man_t *pCombMan, bool fComp);
  /** 
   * Duplicate an AIG but
   * keep only single po nPo 
   * or no po if nPo is -1
   * remove registers unless fKeepRegs is true
   */
  Aig_Man_t *Aig_ManDupSinglePo (Aig_Man_t *p, int nPo,
                                      bool fKeepRegs=true);
  
  inline Aig_Man_t *Aig_ManDupNoPo (Aig_Man_t *p)
  { return Aig_ManDupSinglePo (p, -1, true); }
  

  /** 
   * Duplicate an Aig via Gia 
   */
  Aig_Man_t *Aig_ManGiaDup (Aig_Man_t *pAig);
  
  /** 
   * Rebuild an Aig via Gia and deallocate the old one
   */
  Aig_Man_t *Aig_ManRebuild (Aig_Man_t **ppAig);

  bool Aig_ObjDbgCompare (Aig_Obj_t *pObj1, Aig_Obj_t *pObj2);
  /**
   * Structurally compare two Aig for debugging
   */
  bool Aig_ManDbgCompare (Aig_Man_t *pAig1, Aig_Man_t *pAig2);

  /**
   * Generic simplification
   */
  Aig_Man_t *Aig_ManSimplifyComb (Aig_Man_t *p);
  

  /**
   * Insert a reset PI, called r.
   * When r is true, the registers are reset to 0
   */
  Aig_Man_t *Aig_AddResetPi (Aig_Man_t *p);

  /**
   * Insert a stuttering Pi called r.
   * When r is true, the registers do not change
   */
  Aig_Man_t *Aig_AddStutterPi (Aig_Man_t *p);

  /**
   * Duplicate and stutter the unique first Po
   * stick-on-error
   */
  Aig_Man_t *Aig_AddStutterPo (Aig_Man_t *p);

  /**
   * Create an AIG with PO = AND (!PI_0, ..., !PI_N)
   */
  Aig_Man_t *Aig_CreateAllZero (unsigned nPiNum);
 
}



#endif /* _AIGUTILS_H_ */

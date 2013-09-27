#ifndef _SAFETYVC_H_
#define _SAFETYVC_H_

#include "AigUtils.h"
#include "ItpSatSolver.h"
#include "sat/cnf/cnf.h"
#include "aig/saig/saig.h"

#include "Unroller.h"
namespace avy
{
  /// smart pointer for Cnf_Dat_t. 
  typedef boost::shared_ptr<abc::Cnf_Dat_t> CnfPtr;
  namespace 
  { 
    struct cnf_deleter
    { void operator() (abc::Cnf_Dat_t* p) { if (p) abc::Cnf_DataFree (p); } };
  }
  
  inline CnfPtr cnfPtr (abc::Cnf_Dat_t *p) { return CnfPtr (p, cnf_deleter()); }

  /// Lifts Cnf for the lifetime of the instance
  class ScoppedCnfLift 
  {
    CnfPtr &m_Cnf;
    int m_nOffset;
               
  public:
    ScoppedCnfLift (CnfPtr &cnf, int nOffset) : m_Cnf(cnf), m_nOffset(nOffset)
    { Cnf_DataLift (&*m_Cnf, m_nOffset); }
    ~ScoppedCnfLift () { Cnf_DataLift (&*m_Cnf, -m_nOffset); }
  };
  

  /**
   * Safety Verification Condition: encodes Init & Tr^i & Bad
   * Tr is given by an Aig with a single Po
   * Bad is the driver of the Po of Tr
   * Init is zero for all registers
   */
  class SafetyVC
  {

    /// the original circuit
    AigManPtr m_Circuit;
    /// transition relation part of the circuit
    AigManPtr m_Tr;  
    /// the bad state
    AigManPtr m_Bad;

    /// Cnf of Tr
    CnfPtr m_cnfTr;
    
    /// Cnf of Bad sates
    CnfPtr m_cnfBad;

    /// initialize given a circuit
    void init (abc::Aig_Man_t *pCircuit);

  public:
    /// create a VC given from a circuit. Init is implicit.
    SafetyVC(abc::Aig_Man_t *pCircuit) { init (pCircuit); }
    

    AigManPtr getTr () { return m_Tr; }
    AigManPtr getBad () { return m_Bad; }

    template <typename S>
    void addTr (Unroller<S> &unroller)
    {
      unsigned nOff = unroller.freshBlock (m_cnfTr->nVars);
      ScoppedCnfLift scLift (m_cnfTr, nOff);

      AVY_ASSERT (Vec_IntSize (unroller.getInputs (unroller.frame ())) == 0 &&
                  "Unexpected inputs");
      AVY_ASSERT (Vec_IntSize (unroller.getOutputs (unroller.frame ())) == 0 &&
                  "Unexpected outputs");

      if (unroller.frame () == 0)
        {
          // add clauses for Init
          Aig_Obj_t *pObj;
          int i;
          lit Lits[1];
        
          Saig_ManForEachLo (&*m_Tr, pObj, i)
            {
              Lits[0] = toLitCond (m_cnfTr->pVarNums [pObj->Id], 1);
              unroller.addClause (Lits, Lits + 1);
            }
        }
      else
        {
          Aig_Obj_t *pObj;
          int i;
          Saig_ManForEachLo (&*m_Tr, pObj, i)
            unroller.addInput (m_cnfTr->pVarNums [pObj->Id]);

          // glue new In to old Out
          unroller.glueOutIn ();
        }
      
      // -- add transition relation
      unroller.addCnf (&*m_cnfTr);
      

      // -- register frame outputs
      Aig_Obj_t *pObj;
      int i;
      Saig_ManForEachLi (&*m_Tr, pObj, i)
        unroller.addOutput (m_cnfTr->pVarNums [pObj->Id]);
    }
    
    template <typename S>
    void addBad (Unroller<S> &unroller)
    {
      unsigned nOff = unroller.freshBlock (m_cnfBad->nVars);
      ScoppedCnfLift scLift (m_cnfBad, nOff);

      AVY_ASSERT (Vec_IntSize (unroller.getInputs (unroller.frame ())) == 0 &&
                  "Unexpected inputs");
      AVY_ASSERT (Vec_IntSize (unroller.getOutputs (unroller.frame ())) == 0 &&
                  "Unexpected outputs");
      
      // -- register inputs
      Aig_Obj_t *pCi;
      int i;
      Aig_ManForEachCi (&*m_Bad, pCi, i)
        {
          // -- skip Ci that corresponds to Pi of Tr
          if (i < Saig_ManPiNum (&*m_Tr)) continue;
          unroller.addInput (m_cnfBad->pVarNums [pCi->Id]);
        }

      // -- glue
      unroller.glueOutIn ();

      // -- add bad states
      unroller.addCnf (&*m_cnfBad);

      // -- assert bad output
      lit Lit = toLit (m_cnfBad->pVarNums [Aig_ManCo (&*m_Bad, 0)->Id]);
      unroller.addClause (&Lit, &Lit+1);
    }
    
  };
}



#endif /* _SAFETYVC_H_ */

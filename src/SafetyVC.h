#ifndef _SAFETYVC_H_
#define _SAFETYVC_H_

#include "AigUtils.h"
#include "ItpSatSolver.h"
#include "sat/cnf/cnf.h"

namespace avy
{

  typedef boost::shared_ptr<abc::Cnf_Dat_t> CnfPtr;
  namespace 
  {
    struct cnf_deleter
    {
      void operator() (abc::Cnf_Dat_t* p) { if (p) abc::Cnf_DataFree (p); } 
    };
  }
  
  inline CnfPtr cnfPtr (abc::Cnf_Dat_t *p) { return CnfPtr (p, cnf_deleter()); }

  /**
   * Safety Verification Condition: decide satisfiability of Init & Tr^i & Bad
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


    /** Cnf */

    /// Cnf of Tr
    CnfPtr m_cnfTr;
    
    /// Cnf of Bad sates
    CnfPtr m_cnfBad;


    /// initialize given a circuit
    void init (abc::Aig_Man_t *pCircuit);

    /// Add Cnf for the glue between frame nFrame and nFrame+1
    /// \param nOldOffset is the offset at which Tr of nFrame was added
    /// \param nNewOffset is the offset from which new Cnf vars can be allocated
    /// \return new offset for Cnf vars. Should be nNewOffset if glue does not consume vars
    unsigned addGlueCnf (ItpSatSolver &solver, unsigned nFrame, 
                         unsigned nOldOffset, unsigned nNewOffset);


  public:
    /// create a VC given from a circuit. Init is implicit.
    SafetyVC(abc::Aig_Man_t *pCircuit) { init (pCircuit); }
    

    /// number of Cnf variables needed for the Tr of nFrame
    unsigned cnfVarSize (unsigned nFrame) { return m_cnfTr->nVars; }
    
    /// number of Cnf variables for Bad
    unsigned badVarSize () { return m_cnfBad->nVars; }
    
    
    /** Add Cnf of one Tr to the solver
     *
     * Cnf for Frame0 is Init&Tr
     * Cnf for all other frames is Tr
     *
     * Suggested usage
     * unsigned nOffset = 0; for (i = 0 to N) nOffset += addTrCnf (i); nOffset += addBadCnf (nOffset)
     *
     * \param solver  Sat solver
     * \param nFrame frame to add. 0 means initial
     * \param nOffset offset to allocate CNF variables from
     * \return next free Cnf variable
     */
    unsigned addTrCnf (ItpSatSolver &solver, unsigned nFrame, unsigned nOffset);
    unsigned addBadCnf (ItpSatSolver &solver, unsigned nOffset);


  };
 }



#endif /* _SAFETYVC_H_ */

#ifndef _SAFETYVC_H_
#define _SAFETYVC_H_

#include "AigUtils.h"
#include "ItpSatSolver.h"
#include "sat/cnf/cnf.h"
#include "aig/saig/saig.h"

#include "Unroller.h"
#include "boost/foreach.hpp"

#include <vector>
namespace avy
{
  using namespace avy::abc;
  /// smart pointer for Cnf_Dat_t. 
  typedef boost::shared_ptr<Cnf_Dat_t> CnfPtr;
  namespace 
  { 
    struct cnf_deleter
    { void operator() (Cnf_Dat_t* p) { if (p) Cnf_DataFree (p); } };
  }
  
  inline CnfPtr cnfPtr (Cnf_Dat_t *p) { return CnfPtr (p, cnf_deleter()); }

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

    /// Tr of the 0 frame
    AigManPtr m_Tr0;
    
    /// Cnf of Tr
    CnfPtr m_cnfTr;
    
    /// Cnf of Bad sates
    CnfPtr m_cnfBad;
    
    /// Cnf of Tr0
    CnfPtr m_cnfTr0;

    typedef std::vector<lit> Clause;
    typedef std::vector<Clause> Clauses;
    std::vector<Clauses> m_preCond;
    std::vector<Clauses> m_postCond;

    /// initialize given a circuit
    void init (Aig_Man_t *pCircuit);

  public:
    /// create a VC given from a circuit. Init is implicit.
    SafetyVC(Aig_Man_t *pCircuit) { init (pCircuit); }
    

    AigManPtr getTr () { return m_Tr; }
    AigManPtr getBad () { return m_Bad; }

    
    void resetPreCond () { m_preCond.clear (); }
    void resetPostCond () { m_postCond.clear (); }

    template<typename Iterator>
    void addCondClause (std::vector<Clauses> &clausesByFrame,
                        Iterator bgn, Iterator end, unsigned nFrame, 
                        bool fCompl = false)
    {
      AVY_ASSERT (nFrame > 0);
      
      LOG("learnt", 
          logs () << "CLS at " << nFrame << ": ";
          BOOST_FOREACH (lit Lit, std::make_pair (bgn, end))
          {
            if (Lit == -1) continue;
            if (lit_sign (Lit)) logs () << "-";
            logs () << lit_var (Lit) << " ";
          }
          logs () << "\n";
          );

      clausesByFrame.resize (nFrame + 1);
      Clauses &clauses = clausesByFrame [nFrame];
      clauses.resize (clauses.size () + 1);
      for (Iterator it = bgn; it != end; ++it)
        {
          if (*it == -1) continue;
          lit Lit = *it;
          if (fCompl) Lit = lit_neg (Lit);
          clauses.back ().push_back (Lit);
        }      

      LOG("learnt2", 
          logs () << "CLS at " << nFrame << ": ";
          BOOST_FOREACH (lit Lit, clauses.back ())
          {
            if (lit_sign (Lit)) logs () << "-";
            logs () << lit_var (Lit) << " ";
          }
          logs () << "\n";
          );

    }

    
    /**
       Add a (optinally negated) clause to the pre-condition at a given frame
     */
    template<typename Iterator>
    void addPreCondClause (Iterator bgn, Iterator end, unsigned nFrame, 
                           bool fCompl = false)
    {
      AVY_ASSERT (nFrame > 0);
      addCondClause (m_preCond, bgn, end, nFrame, fCompl);
    }

    /** 
     * Add a (optionally negated) clause to the post-condition at a given frame
     */
    template<typename Iterator>
    void addPostCondClause (Iterator bgn, Iterator end, unsigned nFrame, 
                            bool fCompl = false)
    {
      addCondClause (m_postCond, bgn, end, nFrame, fCompl);
    }
    
    template<typename S>
    boost::tribool addClauses (Unroller<S> &unroller, Clauses &clauses, 
                               Vec_Int_t* vMap)
    {
      boost::tribool res = true;
      Clause tmp;
      BOOST_FOREACH (Clause &cls, clauses)
        {
          tmp.clear ();
          BOOST_FOREACH (lit Lit, cls)
            {
              // map literal based on vMap
              int reg = lit_var (Lit);
              tmp.push_back (toLitCond (Vec_IntEntry (vMap, reg), lit_sign (Lit)));
            }
          res = res && unroller.addClause (&tmp[0], &tmp[0] + tmp.size ());
        }
      return res;
    }
    

    template <typename S>
    void addTr (Unroller<S> &unroller)
    {
      unsigned nFrame = unroller.frame ();
      if (nFrame == 0) addTr0 (unroller);
      else addTrN (unroller);

      /** post-condition clauses */
      if (unroller.frame () < m_postCond.size ())
        addClauses (unroller, m_postCond [nFrame], unroller.getOutputs (nFrame));
    }

  private:
    template <typename S>
    void addTr0 (Unroller<S> &unroller)
    {
      unsigned nOff = unroller.freshBlock (m_cnfTr0->nVars);
      ScoppedCnfLift scLift (m_cnfTr0, nOff);

      unsigned nFrame = unroller.frame ();

      AVY_ASSERT (Vec_IntSize (unroller.getInputs (nFrame)) == 0 &&
                  "Unexpected inputs");
      AVY_ASSERT (Vec_IntSize (unroller.getOutputs (nFrame)) == 0 &&
                  "Unexpected outputs");        
      AVY_ASSERT (nFrame == 0);
      
      // add clauses for Init
      Aig_Obj_t *pObj;
      int i;
      lit Lits[1];
        
      Saig_ManForEachLo (&*m_Tr0, pObj, i)
        {
          Lits[0] = toLitCond (m_cnfTr0->pVarNums [pObj->Id], 1);
          unroller.addClause (Lits, Lits + 1);
        }

      unroller.addCnf (&*m_cnfTr0);

      // -- register frame PIs
      Saig_ManForEachPi (&*m_Tr0, pObj, i)
        // Need to skip the first input
        if (i > 0)
          unroller.addPrimaryInput (m_cnfTr0->pVarNums [pObj->Id]);

      // -- register frame outputs
      Saig_ManForEachLi (&*m_Tr0, pObj, i)
        unroller.addOutput (m_cnfTr0->pVarNums [pObj->Id]);

    }


    template <typename S>
    void addTrN (Unroller<S> &unroller)
    {
      unsigned nOff = unroller.freshBlock (m_cnfTr->nVars);
      ScoppedCnfLift scLift (m_cnfTr, nOff);

      unsigned nFrame = unroller.frame ();

      AVY_ASSERT (Vec_IntSize (unroller.getInputs (nFrame)) == 0 &&
                  "Unexpected inputs");
      AVY_ASSERT (Vec_IntSize (unroller.getOutputs (nFrame)) == 0 &&
                  "Unexpected outputs");        
      AVY_ASSERT (nFrame > 0);
      
      // -- register frame PIs
      Aig_Obj_t *pObj;
      int i;
      Saig_ManForEachPi (&*m_Tr, pObj, i)
        unroller.addPrimaryInput (m_cnfTr->pVarNums [pObj->Id]);

      // -- register inputs
      Saig_ManForEachLo (&*m_Tr, pObj, i)
        unroller.addInput (m_cnfTr->pVarNums [pObj->Id]);

      // glue new In to old Out
      unroller.glueOutIn ();

      /** pre-condition clauses */
      if (nFrame < m_preCond.size ())
        addClauses (unroller, m_preCond [nFrame], unroller.getInputs (nFrame));

      // -- add transition relation
      unroller.addCnf (&*m_cnfTr);

      // -- register frame outputs
      Saig_ManForEachLi (&*m_Tr, pObj, i)
        unroller.addOutput (m_cnfTr->pVarNums [pObj->Id]);
    }
    
  public:
    
    template <typename S>
    void addBad (Unroller<S> &unroller)
    {
      unsigned nOff = unroller.freshBlock (m_cnfBad->nVars);
      ScoppedCnfLift scLift (m_cnfBad, nOff);

      unsigned nFrame = unroller.frame ();

      AVY_ASSERT (Vec_IntSize (unroller.getInputs (nFrame)) == 0 &&
                  "Unexpected inputs");
      AVY_ASSERT (Vec_IntSize (unroller.getOutputs (nFrame)) == 0 &&
                  "Unexpected outputs");
      
      // -- register inputs
      Aig_Obj_t *pCi;
      int i;
      Aig_ManForEachCi (&*m_Bad, pCi, i)
        {
          // -- skip Ci that corresponds to Pi of Tr
          if (i < Saig_ManPiNum (&*m_Tr0))
          {
            // Need to skip the first input
            if (i > 0)
              unroller.addPrimaryInput(m_cnfBad->pVarNums [pCi->Id]);
          }
          else unroller.addInput (m_cnfBad->pVarNums [pCi->Id]);
        }

      // -- glue
      unroller.glueOutIn ();

      /** pre-condition clauses */
      if (nFrame < m_preCond.size ())
        addClauses (unroller, m_preCond [nFrame], unroller.getInputs (nFrame));


      // -- add bad states
      unroller.addCnf (&*m_cnfBad);

      // -- assert bad output
      lit Lit = toLit (m_cnfBad->pVarNums [Aig_ManCo (&*m_Bad, 0)->Id]);
      unroller.setBadLit (Lit);
    }
    
  };
}



#endif /* _SAFETYVC_H_ */

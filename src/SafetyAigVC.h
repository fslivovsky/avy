#ifndef _SafetyAigVC_H_
#define _SafetyAigVC_H_


//#include "boost/noncopyable.hpp"
//#include "boost/logic/tribool.hpp"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"

#include "AigUtils.h"
#include "SafetyVC.h"
#include "sat/cnf/cnf.h"
#include "aig/saig/saig.h"

#include "Unroller.h"
#include "boost/foreach.hpp"

#include <vector>
namespace avy
{
  using namespace avy::abc;

  /**
   * Safety Verification Condition: encodes Init & Tr^i & Bad
   * Tr is given by an Aig with a single Po
   * Bad is the driver of the Po of Tr
   * Init is zero for all registers
   */
  class SafetyAigVC
  {

    /// the original circuit
    AigManPtr m_Circuit;
    AigManPtr m_MasterTr;
    /// transition relation part of the circuit
    /// TODO: For now, storing TRs as vector for frame 1 and up (0 is saved differently)
    /// Should change that and figure out what to do to be more efficient
    std::vector<AigManPtr> m_Tr;
    /// the bad state
    AigManPtr m_Bad;
    
    /// Cnf of Bad sates
    CnfPtr m_cnfBad;

    typedef std::vector<lit> Clause;
    typedef std::vector<Clause> Clauses;
    std::vector<Clauses> m_preCond;
    std::vector<Clauses> m_postCond;

    std::vector<std::vector<boost::tribool> > m_frameVals;

    /// initialize given a circuit
    void init (Aig_Man_t *pCircuit);

    void computeNextTr()
    {
    	Aig_TernarySimulate(&*m_MasterTr, m_frameVals.size(), m_frameVals);
    	Aig_Man_t* pNewTr = Aig_DupWithCiVals(&*m_MasterTr, m_frameVals.back());
    	//std::vector<int> equivClasses;
    	//Aig_Man_t* pSimpTr = Aig_SatSweep(pNewTr, equivClasses);
    	//Aig_ManStop(pNewTr);
    	m_Tr.push_back(aigPtr(pNewTr));
    }

  public:
    /// create a VC given from a circuit. Init is implicit.
    SafetyAigVC(Aig_Man_t *pCircuit)
    {
    	m_frameVals.resize(1);
    	m_frameVals[0].resize(Saig_ManRegNum(pCircuit), false);
    	init (pCircuit);
    }
    

    AigManPtr getTr (unsigned nFrame) { AVY_ASSERT(nFrame < m_Tr.size()); return m_Tr[nFrame]; }
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
        while (m_Tr.size() <= nFrame)
      	  computeNextTr();

        CnfPtr cnfTr = cnfPtr (Cnf_Derive (&*m_Tr[nFrame], Aig_ManRegNum (&*m_Tr[nFrame])));
        unsigned nOff = unroller.freshBlock (cnfTr->nVars);
        Cnf_DataLift(&*cnfTr, nOff);

        AVY_ASSERT (Vec_IntSize (unroller.getInputs (nFrame)) == 0 &&
                    "Unexpected inputs");
        AVY_ASSERT (Vec_IntSize (unroller.getOutputs (nFrame)) == 0 &&
                    "Unexpected outputs");
        //AVY_ASSERT (nFrame > 0);

        // -- add transition relation
        unroller.addCnf (&*cnfTr);

        // -- register frame PIs
        Aig_Obj_t *pObj;
        int i;
        Saig_ManForEachPi (&*m_Tr[nFrame], pObj, i)
          unroller.addPrimaryInput (cnfTr->pVarNums [pObj->Id]);

        if (nFrame > 0)
        {
      	  // -- register inputs
  		  Saig_ManForEachLo (&*m_Tr[nFrame], pObj, i)
  			unroller.addInput (cnfTr->pVarNums [pObj->Id]);

  		  // glue new In to old Out
  		  unroller.glueOutIn ();

  		  /** pre-condition clauses */
  		  if (nFrame < m_preCond.size ())
  			addClauses (unroller, m_preCond [nFrame], unroller.getInputs (nFrame));
        }

        // -- register frame outputs
        Saig_ManForEachLi (&*m_Tr[nFrame], pObj, i)
          unroller.addOutput (cnfTr->pVarNums [pObj->Id]);


        /** post-condition clauses */
        if (unroller.frame () < m_postCond.size ())
            addClauses (unroller, m_postCond [nFrame], unroller.getOutputs (nFrame));
    }

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
      Aig_Obj_t *pObj;
      int i;
      Aig_ManForEachCi (&*m_Bad, pObj, i)
        {
          // -- skip Ci that corresponds to Pi of Tr
          if (i < Saig_ManPiNum (&*m_MasterTr))
            unroller.addPrimaryInput(m_cnfBad->pVarNums [pObj->Id]);
          else unroller.addInput (m_cnfBad->pVarNums [pObj->Id]);
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
    
    const std::vector<boost::tribool>& getLatchesValues(unsigned nFrame) const
	{
    	AVY_ASSERT(m_frameVals.size() > nFrame);
    	return m_frameVals[nFrame];
	}

  };
}



#endif /* _SafetyAigVC_H_ */

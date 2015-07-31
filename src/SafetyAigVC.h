#ifndef _SafetyAigVC_H_
#define _SafetyAigVC_H_


//#include "boost/noncopyable.hpp"
//#include "boost/logic/tribool.hpp"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"

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
    std::vector<CnfPtr> m_TrCnf;

    /// the bad state
    AigManPtr m_Bad;
    
    /// Cnf of Bad sates
    CnfPtr m_cnfBad;

    typedef std::vector<lit> Clause;
    typedef std::vector<Clause> Clauses;
    std::vector<Clauses> m_preCond;
    std::vector<Clauses> m_postCond;

    std::vector<std::vector<boost::tribool> > m_frameVals;
    std::vector<std::vector<int> > m_frameEquivs;

    std::vector<std::vector<int> > m_AigToSat;

    std::vector<int> m_StartingRoots;

    /// initialize given a circuit
    void init (Aig_Man_t *pCircuit);

    void computeNextTr()
    {
    	if (gParams.opt_bmc)
    	{
          AVY_MEASURE_FN;
          // TODO: TrCp not used for now. Need to see if it makes SatSweep more efficient
          //Aig_TernarySimulate(&*m_MasterTr, m_frameVals.size(), m_frameVals);
          //AigManPtr pTrCp = aigPtr (Aig_DupWithCiVals(&*m_MasterTr, m_frameVals.back()));
          AigManPtr pNewTr = aigPtr (Aig_DupWithCiEquivs(&*m_MasterTr,
                                                         m_frameEquivs.back()));

          m_frameEquivs.push_back (std::vector<int>());
          Aig_Man_t* pSimpTr = Aig_SatSweep(&*pNewTr, m_frameEquivs.back());
          m_Tr.push_back(aigPtr(pSimpTr));
    	}
    	else
          m_Tr.push_back(m_MasterTr);
    }

    template <typename S>
    CnfPtr getCnfTr(Unroller<S> &unroller, unsigned nFrame)
    {
        AVY_MEASURE_FN;
        if (m_TrCnf.size() > nFrame) return m_TrCnf[nFrame];
        AVY_ASSERT(m_TrCnf.size() == nFrame);
        CnfPtr cnfTr = cnfPtr (Cnf_Derive (&*m_Tr[nFrame], Aig_ManRegNum (&*m_Tr[nFrame])));
		//unsigned nOff = unroller.freshBlock (cnfTr->nVars);
		//Cnf_DataLift(&*cnfTr, nOff);
        m_TrCnf.push_back(cnfTr);
        m_AigToSat.push_back(std::vector<int>((&*cnfTr)->nVars, -1));

        // Set variables for INPUTS
        Aig_Obj_t *pObj;
		int i;
		Aig_ManForEachCi (&*m_Tr[nFrame], pObj, i)
			m_AigToSat.back()[(&*cnfTr)->pVarNums[pObj->Id]] = unroller.freshVar();

		return cnfTr;
    }

  public:
    /// create a VC given from a circuit. Init is implicit.
    SafetyAigVC(Aig_Man_t *pCircuit)
    {
    	m_frameVals.resize(1);
    	m_frameVals[0].resize(Saig_ManRegNum(pCircuit +(gParams.stick_error ? 1 : 0)), false);
    	init (pCircuit);
    }
    
    void resetSat()
	{
		for(int i=0; i < m_AigToSat.size(); i++)
			m_AigToSat[i].clear();
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
                               Vec_Int_t* vMap, int nFrame = -1)
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
          res = res && unroller.addClause (&tmp[0], &tmp[0] + tmp.size (), nFrame);
        }
      return res;
    }
    

    template <typename S>
    void addTr (Unroller<S> &unroller)
    {
        unsigned nFrame = unroller.frame ();
        while (m_Tr.size() <= nFrame)
      	  computeNextTr();

        CnfPtr cnfTr = getCnfTr(unroller, nFrame);

        AVY_ASSERT (Vec_IntSize (unroller.getInputs (nFrame)) == 0 &&
                    "Unexpected inputs");
        AVY_ASSERT (Vec_IntSize (unroller.getOutputs (nFrame)) == 0 &&
                    "Unexpected outputs");
        //AVY_ASSERT (nFrame > 0);

        std::vector<std::vector<int> > roots;
        findCoiRoots(nFrame, roots);

        // -- register frame PIs
        Aig_Obj_t *pObj;
        int i;
        Saig_ManForEachPi (&*m_Tr[nFrame], pObj, i)
          unroller.addPrimaryInput (cnfTr->pVarNums [pObj->Id]);

        if (nFrame > 0)
        {
      	  // -- register inputs
  		  Saig_ManForEachLo (&*m_Tr[nFrame], pObj, i)
  			unroller.addInput (m_AigToSat[nFrame][cnfTr->pVarNums [pObj->Id]]);

  		  unroller.setFrozenInputs(nFrame, true);
  		  /** pre-condition clauses */
  		  if (nFrame < m_preCond.size ())
  			  addClauses (unroller, m_preCond [nFrame], unroller.getInputs (nFrame));
        }
        else
        {
        	if (gParams.opt_bmc == false)
			{
				// add clauses for Init
				Aig_Obj_t *pObj;
				int i;
				lit Lits[1];

				Saig_ManForEachLo (&*m_Tr[nFrame], pObj, i)
				{
					int var = m_AigToSat[nFrame][cnfTr->pVarNums [pObj->Id]];
					if (var > -1)
					{
						Lits[0] = toLitCond (var, 1);
						unroller.addClause (Lits, Lits + 1);
					}
				}
			}
        }

        // -- add transition relation
		for (int f = nFrame; f >= 0; f--)
		{
			// Add needed clauses according to COI
			unroller.addCoiCnf(f, &*(m_Tr[f]), roots[f], m_TrCnf[f], m_AigToSat[f]);
			// -- Update frame outputs
			Vec_Int_t* pOutputs = unroller.getOutputs(f);
			Vec_IntClear(pOutputs);
			Aig_Obj_t *pObj;
			int i;
			Saig_ManForEachLi (&*m_Tr[f], pObj, i)
			{
			  int var = m_AigToSat[f][m_TrCnf[f]->pVarNums [pObj->Id]];
			  //if (var > -1) printf("i=%d, var=%d\n", i, var);
			  Vec_IntPush(pOutputs, var);
			}

			// Update the glue variables
			if (f < nFrame && f >= 0) {
				unroller.glueOutIn(f+1);
			}
			if (f > 0 && f < m_preCond.size ()) {
			  addClauses (unroller, m_preCond [f], unroller.getInputs (f), f);
			}
		}

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

    std::vector<std::vector<int> >& getFrameEquivs() { return m_frameEquivs; }

    void resimplifyFrame(Aig_Man_t* pConstraints, unsigned nFrame);

    void findCoiRoots(unsigned nFrame, std::vector<std::vector<int> >& roots);

  };
}



#endif /* _SafetyAigVC_H_ */

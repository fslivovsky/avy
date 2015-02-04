#include "SafetyAigVC.h"
#include "AigPrint.h"

#include "aig/saig/saig.h"

using namespace std;
using namespace avy;
using namespace avy::abc;

namespace avy
{

  void SafetyAigVC::init (Aig_Man_t *pCircuit)
  {
    AVY_ASSERT (Saig_ManPoNum(pCircuit) - Saig_ManConstrNum(pCircuit) == 1);
    AVY_ASSERT (Saig_ManConstrNum(pCircuit) == 0);

    // XXX HACK
    // XXX For combinatorial circuits, enable stick_error transformation that adds a latch
    // XXX This converts a combinatorial circuit into a trivial sequential one
    // XXX
    if (Saig_ManRegNum (pCircuit) == 0 && !gParams.stick_error) 
    {
      VERBOSE (2, vout () << "Combinatorial circuit. Enabling stick_error\n";);
      gParams.stick_error = 1;
    }
    
    // -- save circuit
    m_Circuit = aigPtr (Aig_ManDupSimple (pCircuit));//Aig_SatSweep(pCircuit)));


    AigManPtr aig;
    AigManPtr stuckErrorAig;
    if (gParams.stutter)
      aig = aigPtr (Aig_AddStutterPi (&*m_Circuit));
    else 
      {
        if (gParams.stick_error)
          {
            stuckErrorAig = aigPtr (Aig_AddStutterPo (&*m_Circuit));
            aig = stuckErrorAig;
            // XXX HACK XXX
            // Add one extra reg to the INPUT circuit
            //Aig_ObjCreateCi (pCircuit);
            //Aig_ObjCreateCo (pCircuit, Aig_ManConst0 (pCircuit));
            //Aig_ManSetRegNum (pCircuit, pCircuit->nRegs + 1);
            //m_Circuit = aigPtr (Aig_ManDupSimple (pCircuit));
          }
        else
          aig = m_Circuit;

        aig = aigPtr (Aig_AddResetPi (&*aig));
      }
        
    // -- construct Tr 
    Aig_Man_t *pTr = Aig_ManDupNoPo (&*aig);
    Aig_ManRebuild (&pTr);
    m_MasterTr = aigPtr(pTr);
    if (gParams.opt_bmc)
    {
        Aig_Man_t* pNewTr = Aig_DupWithCiVals(pTr, m_frameVals[0]);
        m_frameEquivs.resize(1);
        Aig_Man_t* pSimpTr = Aig_SatSweep(pNewTr, m_frameEquivs[0]);
        Aig_ManStop(pNewTr);
        m_Tr.push_back(aigPtr (pSimpTr));
    }
    else
    	m_Tr.push_back(m_MasterTr);

    //AVY_ASSERT (Saig_ManRegNum (&*m_Tr0) == Saig_ManRegNum (&*m_Tr));

    // -- construct Bad
    Aig_Man_t *pBad = Aig_ManDupSinglePo (&*aig, 0, false);
    Aig_ManRebuild (&pBad);
    m_Bad = aigPtr (pBad);
    m_cnfBad = cnfPtr (Cnf_Derive (&*m_Bad, Aig_ManCoNum (&*m_Bad)));

    // Save the COI of BAD as its AIG is constant throughout the run
    vector<int> startingRoots(1, 0);
	Aig_FindCoiRoots(&*m_Bad, startingRoots, m_StartingRoots);

    LOG ("tr", logs () 
         << "m_Circuit is: " << *m_Circuit << "\n"
         << "m_Tr is: \n " << *m_Tr[0] << "\n"
         << "m_Bad is: " << *m_Bad << "\n";);
  }

  void SafetyAigVC::resimplifyFrame(Aig_Man_t* pConstraints, unsigned nFrame)
  {
	  Aig_Man_t* p = Aig_SatSweepWithConstraints(&*m_Tr[nFrame], pConstraints, m_frameEquivs[nFrame]);
	  m_Tr[nFrame] = aigPtr(p);
  }

  // The function returns the needed COs from each time frame depnding on the
  // given nFrame. The nFrame is the frame that is being checked, meaning, it
  // is represented by BAD.
  // Flow:
  // 1. Find the COI of BAD
  // 2. Go to TR at m_TR[nFrame], where the starting roots are those coming
  //    from BAD. Find the COI and reiterate on m_Tr[nFrame-1]...
  void SafetyAigVC::findCoiRoots(unsigned nFrame, vector<vector<int> >& roots)
  {
	  AVY_ASSERT(roots.size() == 0);

	  // Prepare the vector
	  roots.resize (nFrame + 1);

	  // First set what is required by BAD
	  roots.back().insert(roots.back().begin(), m_StartingRoots.begin(), m_StartingRoots.end());

	  // Get the logic from the TRs. Start at nFrame and go backwards
	  while (nFrame > 0)
	  {
		  AigManPtr pTr = m_Tr[nFrame];
		  vector<int>& start = roots[nFrame];
		  vector<int>& coi = roots[--nFrame];
		  Aig_FindCoiRoots(&*pTr, start, coi);
	  }
  }
}

/*
 * ClsItpSeqMc.cc
 *
 *  Created on: Jul 27, 2013
 *      Author: yakir
 */

#include "ClsItpSeqMc.h"
#include <iostream>

#include "aig/gia/giaAig.h"

using namespace std;

ClsItpSeqMc::ClsItpSeqMc(string strAigFileName) :
      m_McUtil(strAigFileName)
    , m_nLowestModifiedFrame(0)
{
    Pdr_Par_t pdrPars;
    Pdr_ManSetDefaultParams(&pdrPars);

    m_pGlobalPdr = Pdr_ManStart(m_McUtil.getCircuit(), &pdrPars, NULL);
}

bool ClsItpSeqMc::prove()
{
	// Temporary.
	unsigned nMaxFrame = 100;

	// Check the initial states first.

	//if (m_McUtil.setInit() == false)
	//    assert(false);
	// Start the BMC loop
	for (unsigned nFrame = 1; nFrame <= nMaxFrame; nFrame++)
	{
		// Add a frame to the transition relation &
		// Inject clauses if some exist &
		// Solve the resulting formula
		if (solveTimeFrame(nFrame) == FALSIFIED)
		{
			// A CEX is found
		    cout << "Found a CEX at frame: " << nFrame << endl;
			return false;
		}

		cout << "No CEX at frame: " << nFrame << endl;

		// Extract an interpolation-sequence.
		extractInterpolationSeq();

		// Try global push - also check for a fixpoint along the way
		if (globalPush() == true)
		{
			// A fixpoint is reached
			return true;
		}
	}

	return false;
}

ClsItpSeqMc::eMcResult ClsItpSeqMc::solveTimeFrame(unsigned nFrame)
{
    cout << "Solving frame: " << nFrame << endl;
    m_McUtil.startInterpolationSeq(nFrame);
    m_McUtil.reinitializeSAT(nFrame);
    m_McUtil.setInit();
    for (int i = 0; i < nFrame; i++)
    {
        m_McUtil.addTransitionsFromTo(i, i+1);
        m_McUtil.markPartition(i);
        m_McUtil.prepareGlobalVars(i+1);
    }

    m_McUtil.setBad(nFrame);
    m_McUtil.markPartition(nFrame);

    /*Cnf_Dat_t* pCnf = m_McUtil.createCNFRepresentation();
    m_McUtil.updateSATSolverWithCNF(pCnf);
    m_McUtil.destroyCnfRepresentation(pCnf);*/

    eResult res = m_McUtil.solveSat();

    if (res == TRUE)
        return FALSIFIED;
    else if (res == FALSE)
        return BOUNDED;

    return UNKNOWN;
}

bool ClsItpSeqMc::testInterpolationSeq(Aig_Man_t* pInterSeq, int nFrame)
{
    assert(nFrame >= 0);
    Aig_Man_t* pNewBad = m_McUtil.createArbitraryCombMan(pInterSeq, nFrame);
    Aig_Obj_t* pDriver = Aig_ObjChild0(Aig_ManCo(pNewBad,0));
    pDriver = Aig_Not(pDriver);
    Aig_ManCo(pNewBad,0)->pFanin0 = pDriver;
    m_McUtil.setBadMan(pNewBad);
    if (nFrame > 0)
    {
        Aig_Man_t* pNewInit = m_McUtil.createArbitraryCombMan(pInterSeq, nFrame-1);
        m_McUtil.setInitMan(pNewInit);
    }

    m_McUtil.reinitializeSAT(nFrame);
    m_McUtil.setInit();

    m_McUtil.addTransitionsFromTo(0, 1);

    m_McUtil.setBad(1, false);

    eResult res = m_McUtil.solveSat();

    m_McUtil.restoreOrigBad();
    if (nFrame > 0)
        m_McUtil.restoreOrigInit();

    return (res == FALSE);
}

void ClsItpSeqMc::extractInterpolationSeq()
{
    Aig_Man_t* pMan = m_McUtil.getInterpolationSeq();

	// "Skipping" frame 0 since we do not need to do anything with the initial
	// states in terms of clauses.
	unsigned nSize = Aig_ManCoNum(pMan);
	for (unsigned i = 1; i <= nSize; i++)
	{
	    // Test the validity of the interpolation-seq
	    // by checking I_{i-1} & TR => I_i'
	    bool r = testInterpolationSeq(pMan, i-1);
	    assert(r);
	    // Get the interpolant as a set of clauses.
	    transformInterpolantToCNF(i, pMan);

	}

	// Now justify the clauses.
    //justifyClauses(i, cnfInterpolant);
}

void ClsItpSeqMc::transformInterpolantToCNF(
    unsigned nFrame,
    Aig_Man_t* pMan)
{
    // TODO: Decide how to do it.
    // Points to take into account:
    // 1. Do we try and push clauses from previous frame into this frame
    //    before the transformation? Can it help the transformation?

    Pdr_Par_t pdrPars;
    Pdr_ManSetDefaultParams(&pdrPars);

    Aig_Obj_t* pInterpolant = Aig_ManCo(pMan, nFrame-1);
    Aig_Obj_t* pPrev = getFrameAigObj(nFrame-1, pMan);
    Aig_Obj_t* pDriver = Aig_Or(pMan, Aig_ObjChild0(pInterpolant), pPrev);
    pInterpolant->pFanin0 = pDriver;

    Aig_ManDump(pMan);
    // TODO: Check that there is a 1-1 correspondence between latches in the
    // original AIG and in the AIG with the new PO.
    // I don't see why there wouldn't be, but just to make sure.
    // This is due to the fact that we simply use the Cube objects between
    // Global PDR object and the ones used for CNFization. It should be
    // verified that a cube in GlobalPDR is the same in a new PDR instance.
    // It should be as a Cube object is represented by RO numbers and these
    // should be the same between the two AIGs.
    Aig_Man_t *pNewMgr = m_McUtil.duplicateAigWithNewPO(pMan, pInterpolant);
    Gia_Man_t* pGia = Gia_ManFromAigSimple(pNewMgr);
    Aig_ManStop(pNewMgr);
    pNewMgr = Gia_ManToAigSimple(pGia);
    //Aig_ManDump(pNewMgr);
    Pdr_Man_t *pPdrTransform = Pdr_ManStart(pNewMgr , &pdrPars, NULL);

    // In case we are dealing with the first frame, we set up the PDR manager
    // differently.
    // We only want one time frame in the first case, and two in the second.
    // TODO: Should we use 2 and 3 or 1 and 2? Check in DEBUG mode.
    if (nFrame == 1)
    {
        //pdrPars.fVerbose = 1;
        //pdrPars.fMonoCnf = 1;
        //int res = Pdr_ManSolve(pNewMgr, &pdrPars);

        // No other settings in this case.
        Pdr_CNFizationInt(pPdrTransform, m_pGlobalPdr, nFrame-1);
    }
    else
    {
        Pdr_CNFizationInt(pPdrTransform, m_pGlobalPdr, nFrame-1);
    }

}

void ClsItpSeqMc::justifyClauses(unsigned nFrame, const set<Clause>& cnfInterpolant)
{
    // TODO
}

bool ClsItpSeqMc::globalPush()
{
    return false;
}

Aig_Obj_t* ClsItpSeqMc::getFrameAigObj(int nFrame, Aig_Man_t* pMan)
{
    Aig_Man_t* pAig = m_pGlobalPdr->pAig;
    Aig_Obj_t* pRes = Aig_ManConst1(pMan);
    if (nFrame == 0)
    {
        int nRegs = Aig_ManRegNum(pAig);
        assert(nRegs > 0 );
        Aig_Obj_t ** ppInputs = ABC_ALLOC( Aig_Obj_t *, nRegs );

        for ( int i = 0; i < nRegs; i++ )
            ppInputs[i] = Aig_Not( Aig_ManCi(pMan, i) );
        Aig_Obj_t *pRes = Aig_Multi( pMan, ppInputs, nRegs, AIG_OBJ_AND );
        ABC_FREE( ppInputs );
        return pRes;
    }

    Vec_Ptr_t* vVec;
    int i;
    Vec_VecForEachLevelStart( m_pGlobalPdr->vClauses, vVec, i, nFrame-1)
    {
        Pdr_Set_t* pCube;
        int j;
        Vec_PtrForEachEntry( Pdr_Set_t *, vVec, pCube, j )
        {
            Aig_Obj_t* pObj;
            Aig_Obj_t* pClause = Aig_ManConst0(pMan);
            for ( int nLitIdx = 0; nLitIdx < pCube->nLits; nLitIdx++ )
            {
                if ( pCube->Lits[nLitIdx] == -1 )
                    continue;

                pObj = Aig_ManCi(pMan, lit_var(pCube->Lits[nLitIdx]));
                pObj = Aig_NotCond(pObj, !lit_sign(pCube->Lits[i]));
                pClause = Aig_Or(pMan, pClause, pObj);
            }

            pRes = Aig_And(pMan, pRes, pClause);
        }
    }

    return pRes;
}

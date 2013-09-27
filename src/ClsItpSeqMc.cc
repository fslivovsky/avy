/*
 * ClsItpSeqMc.cc
 *
 *  Created on: Jul 27, 2013
 *      Author: yakir
 */

#include "ClsItpSeqMc.h"
#include <iostream>

#include "aig/gia/giaAig.h"
#include "AigPrint.h"
#include "boost/logic/tribool.hpp"
#include "avy/Util/AvyAssert.h"
#include "AigUtils.h"
#include "avy/util/stats.h"

using namespace std;
using namespace avy;

#define SOLVE_TMP 1 // TEMPORARY !!

ClsItpSeqMc::ClsItpSeqMc(string strAigFileName) :
  m_McUtil(strAigFileName) , m_nLowestModifiedFrame(0), 
  m_GlobalPdr (m_McUtil.getCircuit ())
{

}

bool ClsItpSeqMc::prove()
{

    Stats::resume ("mc");
	// Temporary.
	unsigned nMaxFrame = 100;

	// Check the initial states first.

	//if (m_McUtil.setInit() == false)
	//    assert(false);
	// Start the BMC loop
	for (unsigned nFrame = 1; nFrame <= nMaxFrame; nFrame++)
	{
	    Aig_Man_t* pInterSeq;
		// Add a frame to the transition relation &
		// Inject clauses if some exist &
		// Solve the resulting formula
		if (solveTimeFrame(nFrame, &pInterSeq) == FALSIFIED)
		{
			// A CEX is found
		    cout << "Found a CEX at frame: " << nFrame << endl;
			return false;
		}

		cout << "No CEX at frame: " << nFrame << endl;

		// Extract an interpolation-sequence.
		extractInterpolationSeq(pInterSeq);

		// Try global push - also check for a fixpoint along the way
		if (globalPush() == true)
		{
		    m_GlobalPdr.validateInvariant();
			// A fixpoint is reached
		    Stats::stop ("mc");
			return true;

		}
	}

	Stats::stop ("mc");
	return false;
}

#if !SOLVE_TMP
ClsItpSeqMc::eMcResult ClsItpSeqMc::solveTimeFrame(unsigned nFrame, Aig_Man_t** pInterpolationSeq)
{
    cout << "Solving frame: " << nFrame << endl;
    m_McUtil.reinitializeSAT(nFrame);
    m_McUtil.setInit();
    for (int i = 0; i < nFrame; i++)
    {
        m_McUtil.addTransitionsFromTo(i, i+1);
        m_McUtil.markPartition(i);

        if (i+1 < nFrame)
        {
            Vec_Ptr_t* pCubes = Vec_PtrAlloc(10);
            m_GlobalPdr.getCoverCubes(i+1, pCubes);
            m_McUtil.addClausesToFrame(pCubes, i+1);
            Vec_PtrFree(pCubes);
        }

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
    {
        *pInterpolationSeq = m_McUtil.getInterpolationSeq();
        return BOUNDED;
    }

    return UNKNOWN;
}
#endif

bool ClsItpSeqMc::testInterpolationSeq(Aig_Man_t* pInterSeq, int nFrame)
{
    assert(nFrame >= 0);
    Aig_Man_t* pNewBad = m_McUtil.createArbitraryCombMan(pInterSeq, nFrame);
    Aig_Obj_t* pDriver = Aig_ObjChild0(Aig_ManCo(pNewBad,0));
    pDriver = Aig_Not(pDriver);
    Aig_ManCo(pNewBad,0)->pFanin0 = pDriver;

    if (nFrame > 0)
    {
        Aig_Man_t* pNewInit = m_McUtil.createArbitraryCombMan(pInterSeq, nFrame-1);
        m_McUtil.setInitMan(pNewInit);
    }

    m_McUtil.setBadMan(pNewBad);

    m_McUtil.reinitializeSAT(nFrame);
    m_McUtil.setInit();

    m_McUtil.addTransitionsFromTo(0, 1);

    Vec_Ptr_t* pCubes = Vec_PtrAlloc(10);
    m_GlobalPdr.getCoverCubes(nFrame, pCubes);
    m_McUtil.addClausesToFrame(pCubes, 0);
    Vec_PtrFree(pCubes);
    pCubes = Vec_PtrAlloc(10);
    m_GlobalPdr.getCoverCubes(nFrame+1, pCubes);
    m_McUtil.addClausesToFrame(pCubes, 1);
    Vec_PtrFree(pCubes);

    if (m_McUtil.setBad(1, false) == false)
        return true;

    eResult res = m_McUtil.solveSat();

    m_McUtil.restoreOrigBad();
    if (nFrame > 0)
        m_McUtil.restoreOrigInit();

    return (res == FALSE);
}

void ClsItpSeqMc::extractInterpolationSeq(Aig_Man_t* pInterSeq)
{
    LOG("itp", 
        std::cerr << "Interpolation sequence:\n"
        << *pInterSeq << "\n";);
    
        
	// "Skipping" frame 0 since we do not need to do anything with the initial
	// states in terms of clauses.
	unsigned nSize = Aig_ManCoNum(pInterSeq);
	for (unsigned i = 1; i <= nSize; i++)
	{
	    if (Aig_ObjFanin0(Aig_ManCo(pInterSeq, i-1)) == Aig_ManConst1(pInterSeq))
	        continue;

	    // Test the validity of the interpolation-seq
	    // by checking I_{i-1} & TR => I_i'
	    std::cout << "Checking " << i << endl;
	    bool r = testInterpolationSeq(pInterSeq, i-1);
	    assert(r);
	    //Aig_Man_t* pDup = Aig_ManDupSimple(pMan);
	    // Get the interpolant as a set of clauses.
	    transformInterpolantToCNF(i, pInterSeq);
	    //Aig_ManStop(pDup);

        if (m_GlobalPdr.push ()) {
            cerr << "SAFE\n";
            cerr << "validating\n";
            m_GlobalPdr.validateInvariant ();
            break;
        }
        m_GlobalPdr.statusLn (cerr);
	}

	Aig_ManStop(pInterSeq);

	// Now justify the clauses.
        //justifyClauses(i, cnfInterpolant)        
}
void ClsItpSeqMc::transformInterpolantToCNF(
    unsigned nFrame,
    Aig_Man_t* pMan)
{
  using namespace avy;

  Aig_Obj_t* pInterpolant = Aig_ManCo(pMan, nFrame-1);

  LOG("cnf",
      std::cout << "Interpolant for frame: " << nFrame << "\n";
      PrintAig (std::cout, pMan, Aig_ObjChild0(pInterpolant));
      std::cout << "\n\n";);

  Aig_Man_t* pManPrev = Aig_ManStartFrom(pMan);
  Aig_Obj_t* pPrev;

  if (nFrame == 1)
    pPrev = Aig_ManConst0(pManPrev);// m_GlobalPdr.getInit (pMan);
  else
    pPrev = m_GlobalPdr.getCover (nFrame - 1, pManPrev);
  
  pPrev = Aig_ObjCreateCo(pManPrev, pPrev);

  Aig_Man_t* pDupMan = Aig_ManDupSinglePo(pMan, nFrame-1, false);
  AVY_ASSERT(Aig_ManCoNum(pDupMan) == 1);
  //Aig_Man_t* pManOr = createOr(pMan, pInterpolant, pManPrev, pPrev);
  Aig_Man_t* pManOr = Aig_ManCreateMiter(pDupMan, pManPrev, 2);

  Aig_ManStop(pManPrev);
  Aig_ManStop(pDupMan);

  // LOG("cnf",
  //     std::cout << "Cover for frame: " << nFrame-1 << "\n";
  //     std::cout << *pPrev  << "\n\n";);
  
  LOG("cnf",
      std::cout << "Property: \n" << *pManOr << "\n\n";);
  
  Aig_Man_t *pNewMgr = Aig_ManReplacePo(m_McUtil.getCircuit(), pManOr, true);
  Aig_Man_t *pTmp = Aig_ManGiaDup (pNewMgr);
  LOG("gia", Aig_ManDbgCompare (pNewMgr, pTmp););
  Aig_ManStop(pNewMgr);
  pNewMgr = pTmp;
  pTmp = NULL;

  Pdr pdr (pNewMgr);
  Vec_Ptr_t *pCubes = NULL;
  pdr.setLimit (nFrame == 1 ? 2 : 3);
  if (nFrame >= 2)
    {
      pCubes = Vec_PtrAlloc (10);
      m_GlobalPdr.getCoverCubes (nFrame - 1, pCubes);
      pdr.addCoverCubes (1, pCubes);

      Vec_PtrClear (pCubes);
      m_GlobalPdr.getCoverCubes (nFrame, pCubes);
      pdr.addCoverCubes (2, pCubes);
      Vec_PtrFree (pCubes);
      pCubes = NULL;
    }
  pdr.solveSafe ();

    
  pCubes = Vec_PtrAlloc (10);
  pdr.getCoverCubes (nFrame == 1 ? 1 : 2, pCubes);
  m_GlobalPdr.addCoverCubes (nFrame, pCubes);
  Vec_PtrFree (pCubes);
  pCubes = NULL;
}

// void ClsItpSeqMc::transformInterpolantToCNF(
//     unsigned nFrame,
//     Aig_Man_t* pMan)
// {
//     // TODO: Decide how to do it.
//     // Points to take into account:
//     // 1. Do we try and push clauses from previous frame into this frame
//     //    before the transformation? Can it help the transformation?

//     Pdr_Par_t pdrPars;
//     Pdr_ManSetDefaultParams(&pdrPars);

//     Aig_Obj_t* pInterpolant = Aig_ManCo(pMan, nFrame-1);
//     Aig_Obj_t* pPrev = getFrameAigObj(nFrame-1, pMan);
//     Aig_Obj_t* pDriver = Aig_Or(pMan, Aig_ObjChild0(pInterpolant), pPrev);
//     pInterpolant->pFanin0 = pDriver;

//     // TODO: Check that there is a 1-1 correspondence between latches in the
//     // original AIG and in the AIG with the new PO.
//     // I don't see why there wouldn't be, but just to make sure.
//     // This is due to the fact that we simply use the Cube objects between
//     // Global PDR object and the ones used for CNFization. It should be
//     // verified that a cube in GlobalPDR is the same in a new PDR instance.
//     // It should be as a Cube object is represented by RO numbers and these
//     // should be the same between the two AIGs.
//     Aig_Man_t *pNewMgr = m_McUtil.duplicateAigWithNewPO(pMan, pInterpolant);
//     Gia_Man_t* pGia = Gia_ManFromAigSimple(pNewMgr);
//     Aig_ManStop(pNewMgr);
//     pNewMgr = Gia_ManToAigSimple(pGia);
//     //Aig_ManDump(pNewMgr);
//     Pdr_Man_t *pPdrTransform = Pdr_ManStart(pNewMgr , &pdrPars, NULL);

//     // In case we are dealing with the first frame, we set up the PDR manager
//     // differently.
//     // We only want one time frame in the first case, and two in the second.
//     // TODO: Should we use 2 and 3 or 1 and 2? Check in DEBUG mode.
//     if (nFrame == 1)
//     {
//         //pdrPars.fVerbose = 1;
//         //pdrPars.fMonoCnf = 1;
//         //int res = Pdr_ManSolve(pNewMgr, &pdrPars);

//         // No other settings in this case.
//         Pdr_CNFizationInt(pPdrTransform, m_pGlobalPdr, nFrame-1);
//     }
//     else
//     {
//         Pdr_CNFizationInt(pPdrTransform, m_pGlobalPdr, nFrame-1);
//     }

//     Vec_Ptr_t* pCubes = Vec_PtrAlloc(10);
//     m_McUtil.getCubesFromPdrFrame(pPdrTransform, (nFrame == 1) ? 1: 2, pCubes);
//     m_McUtil.addCubesToPdrFrame(m_pGlobalPdr, pCubes, nFrame);
// }

void ClsItpSeqMc::justifyClauses(unsigned nFrame, const set<Clause>& cnfInterpolant)
{
    // TODO
}

bool ClsItpSeqMc::globalPush()
{
  LOG ("pdr",
       cerr << "Global Pdr before push\n" << m_GlobalPdr << "\n";);
  tribool res = m_GlobalPdr.push ();
  AVY_ASSERT (res || !res);

  LOG ("pdr", 
       cerr << "Global Pdr after push\n" << m_GlobalPdr << "\n";);
        
  return res == true;
}

Aig_Man_t* ClsItpSeqMc::createOr(Aig_Man_t* pMan1, Aig_Obj_t* p1, Aig_Man_t* pMan2, Aig_Obj_t* p2)
{
    assert( Aig_ManRegNum(pMan1) == 0 && Aig_ManRegNum(pMan2) == 0 );
    assert(Aig_ManCiNum(pMan1) == Aig_ManCiNum(pMan2));

    // create the new manager
    Aig_Man_t *pNew = Aig_ManStart( Aig_ManObjNumMax(pMan1) + Aig_ManObjNumMax(pMan2) );

    // create the PIs
    Aig_ManCleanData( pMan1 );
    Aig_ManCleanData( pMan2 );
    Aig_ManConst1(pMan1)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pMan2)->pData = Aig_ManConst1(pNew);

    int i;
    Aig_Obj_t * pObj;
    Aig_ManForEachCi( pMan1, pObj, i )
    {
        pObj->pData = Aig_ObjCreateCi( pNew );
        Aig_Obj_t* pObj2 = Aig_ManCi(pMan2, i);
        pObj2->pData = pObj->pData;
    }

    // set registers
    pNew->nTruePis = pMan1->nTruePis;
    pNew->nTruePos = 1;
    pNew->nRegs    = 0;

    // duplicate internal nodes
    Aig_ManForEachNode( pMan1, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );

    Aig_ManForEachNode( pMan2, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );

    pObj = Aig_Or(pNew, Aig_ObjChild0Copy(p1), Aig_ObjChild0Copy(p2));

    // Create the new output
    Aig_ObjCreateCo(pNew, pObj);

    Aig_ManCleanup( pNew );
    Aig_ManCleanData(pMan1);
    Aig_ManCleanData(pMan2);

    return pNew;
}

#if SOLVE_TMP
#define NON_INC 1
ClsItpSeqMc::eMcResult ClsItpSeqMc::solveTimeFrame(unsigned nFrame, Aig_Man_t** pInterpolationSeq)
{
    cout << "Solving frame: " << nFrame << endl;

#if NON_INC
    BMCSolver* pSolver = NULL;
    //if (m_FrameInterpolatingSolvers.size() == 0)
    {
        for (int k=0; k < nFrame-1; k++)
        {
            pSolver = m_FrameInterpolatingSolvers[k];// new BMCSolver(m_McUtil.getCircuit());
            pSolver->reinitializeSAT();
            pSolver->setInterpolationFrame(1);
            if (k == 0)
                pSolver->setInit();
        }
    }
    AVY_ASSERT(nFrame >= 1);
    AVY_ASSERT(m_FrameInterpolatingSolvers.size() == nFrame-1);
    pSolver = new BMCSolver(m_McUtil.getCircuit());
    pSolver->setInterpolationFrame(1);
    if (nFrame == 1)
    {
        pSolver->setInit();
    }

    m_FrameInterpolatingSolvers.push_back(pSolver);
#else
    AVY_ASSERT(nFrame >= 1);
    AVY_ASSERT(m_FrameInterpolatingSolvers.size() == nFrame-1);
    BMCSolver* pSolver = new BMCSolver(m_McUtil.getCircuit());
    pSolver->setInterpolationFrame(1);
    if (nFrame == 1)
    {
        pSolver->setInit();
    }

    m_FrameInterpolatingSolvers.push_back(pSolver);
#endif

    eResult res = UNDEF;
    Aig_Man_t* pInterpolantMan = NULL;
    unsigned nCurrentFrame = nFrame;
    Vec_Ptr_t* vInterpolants = Vec_PtrAlloc(nFrame);
    for(vector<BMCSolver*>::iterator itSolver = m_FrameInterpolatingSolvers.begin();
        itSolver != m_FrameInterpolatingSolvers.end();
        itSolver++)
    {
        AVY_ASSERT(nCurrentFrame >= 1);
        pSolver = *itSolver;

        if (nCurrentFrame < nFrame)
        {
            Stats::resume ("itpseq.itp");
            // Define the init state
            pSolver->setInitMan(pInterpolantMan);
            pSolver->setInit();

            int actual = (nFrame - nCurrentFrame);
            Vec_Ptr_t* pCubes = Vec_PtrAlloc(10);
            m_GlobalPdr.getCoverCubes(actual, pCubes);
            pSolver->addClausesToFrame(pCubes, 0);
        }

#if NON_INC
        for (int k=1; k < nCurrentFrame-1; k++)
        {
            pSolver->addTransitionsFromTo(k, k+1);
        }
#endif

        pSolver->addTransitionsFromTo(nCurrentFrame-1, nCurrentFrame);
        //pSolver->markInitCnfVars();
        pSolver->markClausesForAPart(0);
        //pSolver->markClausesForAPart(1);
        pSolver->setBad(nCurrentFrame);


        for (int k = 0; k < nCurrentFrame-1; k++)
        {
            int actual = (nFrame - nCurrentFrame) + 1 + k;
            Vec_Ptr_t* pCubes = Vec_PtrAlloc(10);
            m_GlobalPdr.getCoverCubes(actual, pCubes);
            pSolver->addClausesToFrame(pCubes, k+1);
        }
        if (nCurrentFrame == nFrame && nFrame > 1)
        {
            //pSolver->solveSatAndGetSeq(pInterpolationSeq);
            //break;
            bool bCont = false;
            for (int yy=nFrame-1; yy >= 1; yy--)
            {
                if (pSolver->solveSat(yy) == FALSE)
                {
                    Aig_Man_t* pAig = pSolver->getCircuit();
                    while (yy > 0)
                    {
                        nCurrentFrame--;
                        if (yy > 1) itSolver++;
                        yy--;
                        pInterpolantMan = Aig_ManStart(Aig_ManCiNum(pAig) + 2);
                        Aig_Obj_t* pObj;
                        int xx;
                        Saig_ManForEachLi(pAig, pObj, xx)
                        {
                            Aig_ObjCreateCi(pInterpolantMan);
                        }
                        Aig_ObjCreateCo(pInterpolantMan, Aig_ManConst1(pInterpolantMan));
                        Vec_PtrPush(vInterpolants, pInterpolantMan);
                    }

                    bCont = true;
                    break;
                }
            }
            if (bCont) continue;
        }
        if (nCurrentFrame == nFrame)
            Stats::resume ("bmc.itp");
        res = pSolver->solveSat();
        if (nCurrentFrame == nFrame)
            Stats::stop ("bmc.itp");
        if (res != FALSE) {
            if (nCurrentFrame < nFrame)
                AVY_ASSERT(false);
            break;
        }
        Aig_Man_t* pTemp = pSolver->getInterpolant();
        pInterpolantMan = Aig_ManSimplifyComb(pTemp);
        Aig_ManStop(pTemp);
        LOG("itp",
                std::cerr << "Interpolant:\n"
                << *pInterpolantMan << "\n";);
        Aig_ManCleanData(pInterpolantMan);
        Vec_PtrPush(vInterpolants, pInterpolantMan);
        nCurrentFrame--;
    }
    if (res == TRUE)
        return FALSIFIED;

    if (Vec_PtrSize(vInterpolants) > 0)
        *pInterpolationSeq = Aig_ManSimplifyComb(Aig_ManDupArray(vInterpolants));
    Aig_ManPrintStats(*pInterpolationSeq);

    int i;
    Vec_PtrForEachEntry(Aig_Man_t*, vInterpolants, pInterpolantMan, i)
    {
        Aig_ManStop(pInterpolantMan);
    }
    Vec_PtrFree(vInterpolants);

    Stats::stop ("itpseq.itp");
#if !NON_INC
    for(vector<BMCSolver*>::iterator itSolver = m_FrameInterpolatingSolvers.begin();
        itSolver != m_FrameInterpolatingSolvers.end();
        itSolver++)
    {
        delete *itSolver;
    }
    m_FrameInterpolatingSolvers.clear();
#endif

    if (res == FALSE)
        return BOUNDED;

    return UNKNOWN;
}
#endif

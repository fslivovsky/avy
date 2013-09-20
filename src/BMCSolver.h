#ifndef ABC_BMC_SOLVER_H
#define ABC_BMC_SOLVER_H

#include "AbcMCInterface.h"

#include "aig/aig/aig.h"
#include "aig/saig/saig.h"
#include "sat/cnf/cnf.h"
#include "base/main/main.h"
#include "base/abc/abc.h"
#include "misc/vec/vec.h"
#include "sat/bsat/satStore.h"
#include "sat/bsat/satSolver2.h"

#include "proof/pdr/pdr.h"
#include "proof/pdr/pdrInt.h"

#include "aig/gia/giaAig.h"
#include "proof/dch/dch.h"

//#include "PeriploContext.h"

#include <string>
#include <vector>
#include <set>
#include <iostream>
#include <sstream>

using namespace abc;
using namespace std;

// An interface to the ABC framework.
// Should give utilities such as:
// 1. Unrolling of a transition relation
// 2. Setting and Getting the initial states
// 3. Generation of CNF formula
//
// Can also be implemented for other frameworks: add an Interface class
// with general utility functions (class BMCSolver : public McInterface).

class BMCSolver
{
public:

    BMCSolver(Aig_Man_t* pAig);

	~BMCSolver()
	{
		Abc_Stop();
	}

	Aig_Man_t* getCircuit() { return m_pAig; }

	// Updates pUnrolledTR to an AIG representing an unrolling of the TR from
	// phase nFrom to phase nTo. It should be possible to create the
	// unrolling in an incremental fashion.
	// NOTE: The property is not asserted in the resulting AIG.
	void addTransitionsFromTo(unsigned nFrom, unsigned nTo);
	bool setInit();
	bool setBad(int nFrame, bool bHasPIs = true);

	bool addCNFToSAT(Cnf_Dat_t *pCnf);

	eResult solveSat();

	Aig_Man_t* getInterpolant();

	void startInterpolationSeq(int nSize)
	{
	    /*if (m_pSat->pInt2 != NULL)
	    {
	        Int2_ManStop(m_pSat->pInt2);
	        m_pSat->pInt2 = NULL;
	    }
	    prepareGlobalVars(nSize);
	    sat_solver2_set_seqsize(m_pSat, nSize);
	    int ** vGlobal = ABC_ALLOC(int*, nSize);
	    int nGloVarsNum = m_GlobalVars[0].size();

	    for (int i = 0; i < nSize; i++)
	    {
	        vGlobal[i] = ABC_ALLOC(int, nGloVarsNum);
	        for (int j = 0; j < nGloVarsNum; j++)
	            vGlobal[i][j] = m_GlobalVars[i][j];
	    }

	    m_pSat->pInt2 = Int2_ManStart( m_pSat, vGlobal, nGloVarsNum );
	    for (int i = 0; i < nSize; i++)
	        ABC_FREE(vGlobal[i]);
	    ABC_FREE(vGlobal);*/
	}

	void reinitializeSAT(int nFrame)
	{
	    m_bTrivial = false;
	    if (m_pSat != NULL) sat_solver2_delete(m_pSat);
	    m_pSat = sat_solver2_new();
        sat_solver2_setnvars( m_pSat, m_pInitCnf->nVars + nFrame*m_pOneTRCnf->nVars + m_pBadCnf->nVars );
        m_nLastFrame = m_iFramePrev = 0;
        m_GlobalVars.clear();
	}

	Aig_Man_t* createArbitraryCombMan(Aig_Man_t* pMan, int nOut);

	void prepareGlobalVars(int nFrame);

	Aig_Man_t* setBadMan(Aig_Man_t* pBad)
	{
	    assert(m_pBadStore == NULL);
	    Aig_Man_t* pTemp = m_pBad;
	    m_pBad = pBad;
	    m_pBadCnfStore = m_pBadCnf;
	    m_pBadCnf = Cnf_Derive(m_pBad, Aig_ManCoNum(m_pBad));

	    m_pBadStore = pTemp;
	    return pTemp;
	}
	Aig_Man_t* setInitMan(Aig_Man_t* pInit)
	{
	    assert(m_pInitStore == NULL);
	    Aig_Man_t* pTemp = m_pInit;
        m_pInit = pInit;
        m_pInitCnfStore = m_pInitCnf;
        m_pInitCnf = Cnf_Derive(m_pInit, 0);

        m_pInitStore = pTemp;
        return pTemp;
	}

	void restoreOrigInit()
	{
	    assert(m_pInitStore != NULL);
	    Aig_ManStop(m_pInit);
	    Cnf_DataFree(m_pInitCnf);
	    m_pInit = m_pInitStore;
	    m_pInitCnf = m_pInitCnfStore;

	    m_pInitStore = NULL;
	    m_pInitCnfStore = NULL;
	}

	void restoreOrigBad()
    {
	    assert(m_pBadStore != NULL);
        Aig_ManStop(m_pBad);
        Cnf_DataFree(m_pBadCnf);
        m_pBad = m_pBadStore;
        m_pBadCnf = m_pBadCnfStore;

        m_pBadStore = NULL;
        m_pBadCnfStore = NULL;
    }

	Aig_Man_t* simplifyCombAig(Aig_Man_t* pMan)
	{
	    Dch_Pars_t pars;
        Dch_ManSetDefaultParams(&pars);
        pars.nWords = 16;
        Gia_Man_t* pGia = Gia_ManFromAigSimple(pMan);
        Aig_ManStop(pMan);
        Gia_Man_t *pSynGia = Gia_ManFraigSweep(pGia, (void*)(&pars));
        Gia_ManStop(pGia);
        Aig_Man_t* pSyn = Gia_ManToAigSimple(pSynGia);
        Gia_ManStop(pSynGia);
        return pSyn;
	}

	void addClausesToFrame(Vec_Ptr_t* pCubes, int nFrame);

	void setInterpolationFrame(int nFrame) { m_nInterpolationFrame = nFrame; }

private:
	Aig_Man_t * duplicateAigWithoutPOs( Aig_Man_t * p );

	void createInitMan();
	void createBadMan();

	bool addClauseToSat(lit* begin, lit* end)
	{
	    int Cid = sat_solver2_addclause(m_pSat, begin, end, -1);

	    if (m_nInterpolationFrame > 0 &&
	        m_nInterpolationFrame == m_nLastFrame)
	    {
	        clause2_set_partA(m_pSat, Cid, 1);
	    }
	    //m_ClausesByFrame[m_nLastFrame].insert(Cid);
	    return (Cid != 0);
	}

	void markCnfVars(Aig_Man_t* pMan, Cnf_Dat_t* pCnf)
	{
	    Aig_Obj_t* pObj;
	    int i;
        Aig_ManForEachObj( pMan, pObj, i )
            if ( pCnf->pVarNums[pObj->Id] >= 0)
                var_set_partA(m_pSat, pCnf->pVarNums[pObj->Id], 1);
                //m_VarsByFrame[m_nLastFrame].insert(pCnf->pVarNums[pObj->Id]);
	}

	unsigned getNumOfGlueRemovalVars(unsigned nFrame)
	{
	    if (m_bAddGlueRemovalLiteral == false) return 0;
	    if (m_nLevelRemoval >= 0) return 1;

	    return nFrame+1;
	}
private:
	Abc_Frame_t* 	      m_pAbcFramework;

	// AIG managers
    Aig_Man_t *           m_pAig;           // The rolled model
    Aig_Man_t *           m_pOneTR;         // An AIG representing one TR
    Aig_Man_t*            m_pBad;           // AIG representing Bad states.
    Aig_Man_t*            m_pInit;          // AIG representing INIT.

    Aig_Man_t*            m_pBadStore;      // AIG representing Bad states.
    Aig_Man_t*            m_pInitStore;     // AIG representing INIT.

    // CNF data
    Cnf_Dat_t*            m_pOneTRCnf;      // CNF representation of one TR
    Cnf_Dat_t*            m_pInitCnf;       // CNF representation of one TR
    Cnf_Dat_t*            m_pBadCnf;        // CNF representation of one TR

    Cnf_Dat_t*            m_pInitCnfStore;  // CNF representation of one TR
    Cnf_Dat_t*            m_pBadCnfStore;   // CNF representation of one TR

    // SAT solver
    sat_solver2*          m_pSat;           // SAT solver

    int                   m_iFramePrev;     // previous frame
    int                   m_nLastFrame;     // last frame

    // Interpolation helpers
    // Need to log which clauses/variables were added for which frames.
    vector<set<int> >     m_ClausesByFrame;
    vector<set<int> >     m_VarsByFrame;

    vector<vector<int> >  m_GlobalVars;

    bool m_bTrivial;

    bool m_bAddGlueRemovalLiteral;
    int m_nLevelRemoval;

    int m_nInterpolationFrame;
};

#endif // ABC_MC_INTERFACE_H

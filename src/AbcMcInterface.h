#ifndef ABC_MC_INTERFACE_H
#define ABC_MC_INTERFACE_H

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

#include "AigUtils.h"
#include "avy/Util/AvyAssert.h"
//#include "PeriploContext.h"

#include <string>
#include <vector>
#include <set>
#include <iostream>
#include <sstream>

using namespace abc;
using namespace std;
using namespace avy;

// An interface to the ABC framework.
// Should give utilities such as:
// 1. Unrolling of a transition relation
// 2. Setting and Getting the initial states
// 3. Generation of CNF formula
//
// Can also be implemented for other frameworks: add an Interface class
// with general utility functions (class AbcMcInterface : public McInterface).

namespace abc
{
  extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, 
                                   int fRegisters );
}


enum eResult {
    FALSE = -1,
    UNDEF = 0,
    TRUE = 1
};

class AbcMcInterface
{
public:

    AbcMcInterface(std::string strFileName);

	~AbcMcInterface()
	{
		Abc_Stop();
	}

	Aig_Man_t* getCircuit() { return m_pAig; }

	// Updates pUnrolledTR to an AIG representing an unrolling of the TR from
	// phase nFrom to phase nTo. It should be possible to create the
	// unrolling in an incremental fashion.
	// NOTE: The property is not asserted in the resulting AIG.
	void addTransitionsFromTo(int nFrom, int nTo);
	bool setInit();
	bool setBad(int nFrame, bool bHasPIs = true);

	bool addCNFToSAT(Cnf_Dat_t *pCnf);

	eResult solveSat();


	Aig_Man_t* getInterpolationSeq();

	void markPartition(int part)
	{
	    sat_solver_store_mark_clauses_a(m_pSat, part);
	}


	void reinitializeSAT(int nFrame)
	{
	    m_bTrivial = false;
	    if (m_pSat != NULL) sat_solver_delete(m_pSat);
	    m_pSat = sat_solver_new();
        sat_solver_store_alloc( m_pSat, nFrame );
        /*m_pSat->nLearntStart = 10000;
        m_pSat->nLearntDelta =  5000;
        m_pSat->nLearntRatio =    75;
        m_pSat->nLearntMax   = m_pSat->nLearntStart;*/
        sat_solver_setnvars( m_pSat, 
                             m_pInitCnf->nVars + 
                             nFrame*m_pOneTRCnf->nVars + 
                             m_pBadCnf->nVars );
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

	void addClausesToFrame(Vec_Ptr_t* pCubes, int nFrame);

private:
  void createInitMan() 
  {m_pInit = Aig_CreateAllZero (Aig_ManRegNum (m_pAig)); }
 
  void createBadMan() 
  {
    AVY_ASSERT (Saig_ManPoNum(m_pAig) - Saig_ManConstrNum(m_pAig) == 1);
    AVY_ASSERT (Saig_ManConstrNum(m_pAig) == 0);

    m_pBad = Aig_ManDupSinglePo (m_pAig, 0, false);
    Aig_ManRebuild (&m_pBad);
  }


	bool addClauseToSat(lit* begin, lit* end)
	{
	    int Cid = sat_solver_addclause(m_pSat, begin, end);

	    //clause2_set_partA(m_pSat, Cid, m_nLastFrame);
	    //m_ClausesByFrame[m_nLastFrame].insert(Cid);
	    return (Cid != 0);
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
    sat_solver*          m_pSat;           // SAT solver

    int                   m_iFramePrev;     // previous frame
    int                   m_nLastFrame;     // last frame

    // Interpolation helpers
    // Need to log which clauses/variables were added for which frames.
    vector<set<int> >     m_ClausesByFrame;
    vector<set<int> >     m_VarsByFrame;

    vector<vector<int> >  m_GlobalVars;

    bool m_bTrivial;
    bool m_bAddGlueRemovalLiteral;
};

#endif // ABC_MC_INTERFACE_H

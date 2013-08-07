#ifndef ABC_MC_INTERFACE_H
#define ABC_MC_INTERFACE_H

#include "aig/aig/aig.h"
#include "aig/saig/saig.h"
#include "sat/cnf/cnf.h"
#include "base/main/main.h"
#include "base/abc/abc.h"
#include "misc/vec/vec.h"
#include "sat/bsat/satStore.h"

#include <string>

using namespace abc;

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
  extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
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

	// Updates pUnrolledTR to an AIG representing an unrolling of the TR from
	// phase nFrom to phase nTo. It should be possible to create the
	// unrolling in an incremental fashion.
	// NOTE: The property is not asserted in the resulting AIG.
	void addTransitionsFromTo(int nFrom, int nTo);
	bool setInit();
	bool setBad(int nFrame);

	bool addCNFToSAT(Cnf_Dat_t *pCnf);

	eResult solveSat();

private:
	Aig_Man_t * duplicateAigWithoutPOs( Aig_Man_t * p );

	void createInitMan();
	void createBadMan();

	Aig_Obj_t* createCombSlice_rec(Aig_Man_t* pMan, Aig_Obj_t * pObj);

private:
	Abc_Frame_t* 	      m_pAbcFramework;

	// AIG managers
    Aig_Man_t *           m_pAig;           // The rolled model
    Aig_Man_t *           m_pOneTR;         // An AIG representing one TR
    Aig_Man_t*            m_pBad;           // AIG representing Bad states.
    Aig_Man_t*            m_pInit;          // AIG representing INIT.

    // CNF data
    Cnf_Dat_t*            m_pOneTRCnf;      // CNF representation of one TR
    Cnf_Dat_t*            m_pInitCnf;       // CNF representation of one TR
    Cnf_Dat_t*            m_pBadCnf;        // CNF representation of one TR

    // SAT solver
    sat_solver *          m_pSat;           // SAT solver

    int                   m_iFramePrev;     // previous frame
    int                   m_nLastFrame;     // last frame
};

#endif // ABC_MC_INTERFACE_H

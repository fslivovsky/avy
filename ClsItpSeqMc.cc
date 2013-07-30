/*
 * ClsItpSeqMc.cc
 *
 *  Created on: Jul 27, 2013
 *      Author: yakir
 */

#include "ClsItpSeqMc.h"
#include <iostream>

using namespace std;

bool ClsItpSeqMc::prove()
{
	// Temporary.
	unsigned nMaxFrame = 100;

	// Check the initial states first.

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
    m_McUtil.addTransitionsFromTo(nFrame-1, nFrame);
    Cnf_Dat_t* pCnf = m_McUtil.createCNFRepresentation();
    m_McUtil.updateSATSolverWithCNF(pCnf);
    m_McUtil.destroyCnfRepresentation(pCnf);

    eResult res = m_McUtil.solveSat();

    if (res == TRUE)
        return FALSIFIED;
    else if (res == FALSE)
        return BOUNDED;

    return UNKNOWN;
}

void ClsItpSeqMc::extractInterpolationSeq()
{
    Aig_Man_t* pMan;
	// Use the SAT solver to get an interpolation sequence.
	// I assume that we can get it as a vector of AIGs (using the same mgr).
	vector<Aig_Obj_t*> interpolationSequence;

	// "Skipping" frame 0 since we do not need to do anything with the initial
	// states in terms of clauses.
	unsigned nSize = interpolationSequence.size();
	for (unsigned i = 1; i <= nSize; i++)
	{
	    // Get the interpolant as a set of clauses.
	    set<Clause> cnfInterpolant;
	    transformInterpolantToCNF(i, pMan, interpolationSequence[i-1], cnfInterpolant);

	    // Now justify the clauses.
	    justifyClauses(i, cnfInterpolant);
	}
}

void ClsItpSeqMc::transformInterpolantToCNF(
    unsigned nFrame,
    Aig_Man_t* pMan,
    Aig_Obj_t* pInterpolant,
    set<Clause>& cnfInterpolant)
{
    // TODO: Decide how to do it.
    // Points to take into account:
    // 1. Do we try and push clauses from previous frame into this frame
    //    before the transformation? Can it help the transformation?
}

void ClsItpSeqMc::justifyClauses(unsigned nFrame, const set<Clause>& cnfInterpolant)
{
    // TODO
}

bool ClsItpSeqMc::globalPush()
{
    return false;
}

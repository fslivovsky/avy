/*
 * ClsItpSeqMc.h
 *
 *  Created on: Jul 27, 2013
 *      Author: yakir
 */

#ifndef CLS_ITP_SEQ_MC_H
#define CLS_ITP_SEQ_MC_H

#include <set>
#include <vector>

#include "AbcMcInterface.h"

#include "proof/pdr/pdr.h"
#include "proof/pdr/pdrInt.h"

using namespace std;

// Fooling the compiler for now
typedef int Clause;

// ************************************************************************
// A class to manage and execute Interpolation-Sequence-like MC algorithm.
// The algorithm is based on BMC, interpolants in CNF, justification,
// clauses propagation, inductive reasoning (a-la inductive generalization)
// The input is an AIG with one output representing one property.
// No support for multiple properties for now - to simplify matters.
//
// Computed over-approximations have the following properties:
// 1. F_0 = INIT
// 2. F_i => P
// 3. F_i => F_{i+1}
// 4. F_i & TR => F'_{i+1}
// ************************************************************************
class ClsItpSeqMc
{
public:
    enum eMcResult {
        FALSIFIED = -1,
        UNKNOWN = 0,
        VERIFIED = 1,
        BOUNDED = 2
    };

public:
	ClsItpSeqMc(string strAigFileName) :
	      m_McUtil(strAigFileName)
        , m_nLowestModifiedFrame(0)
    {

    }

	~ClsItpSeqMc()
	{

	}

	bool prove();

private:
	eMcResult solveTimeFrame(unsigned nFrame);

	// ************************************************************************
	// Given an unsatisfiable BMC formula, extract an interpolation sequence
	// and trasform each of the interpolants into CNF.
	// ************************************************************************
	void extractInterpolationSeq();


	// ************************************************************************
	// Get an interpolant of a specific frame as an AIG and transform to CNF.
	// ************************************************************************
	void transformInterpolantToCNF(
			unsigned nFrame,
			Aig_Man_t* pInterpolantMgr);


	// ************************************************************************
	// Takes a set of clauses representing an interpolant at frame nFrame and
	// justify them. Justified clauses are added to m_ClausesPerFrame.
	// In addition, the procedure takes care of injecting clauses into the
	// SAT solver.
	// ************************************************************************
	void justifyClauses(unsigned nFrame, const set<Clause>& cnfInterpolant);


	// ************************************************************************
	// Try and push a clause from nFrame to nFrame+1
	// In addition, the procedure takes care of injecting clauses into the
	// SAT solver.
	// ************************************************************************
	void localPush(unsigned nFrame, const Clause& cls);


	// ************************************************************************
	// Try to globally push clauses forward.
	// In addition, the procedure takes care of injecting clauses into the
	// SAT solver.
	// ************************************************************************
	bool globalPush();


	// ************************************************************************
	// Test for a fixpoint. Meaning, check if F_{nFrame+1} => F_{nFrame}.
	// ************************************************************************
	bool isFixpoint(unsigned nFrame);


	bool testInterpolationSeq(Aig_Man_t* pInterSeq, int nFrame);


private:
	// Using our own MC interface to ABC.
	// Gives us utilities such as unrolling and SAT solving.
	AbcMcInterface m_McUtil;

	// A global PDR manager.
	// This manager is used as a utility for the following:
	// 1. Store clauses of the different time-frames.
	// 2. Push clauses forward.
	// 3. Check for a fixpoint.
	Pdr_Man_t *m_pGlobalPdr;

	// Given the above manager, those are not needed.
	/*
	// Maintain the sets of learned clauses (generated by CNFization
	// and justification of interpolants).
	vector<std::set<Clause> > m_ClausesPerFrame;

	// Maintain a special set for the globally inductive clauses F_{infinity}
	set<Clause> m_Infinity;
	*/

	// Track modified frames.
	// Don't want to apply reasoning where no meaningfull clauses were added.
	// Still need to figure out if this is possible/needed in our settings.
	unsigned m_nLowestModifiedFrame;
};

#endif // CLS_ITP_SEQ_MC_H

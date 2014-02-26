/*
 * MinisatItpSeq.h
 *
 *  Created on: Jan 20, 2014
 *      Author: yakir
 */

#ifndef MINISAT_ITP_SEQ_H_
#define MINISAT_ITP_SEQ_H_

#include <vector>
#include "core/ProofVisitor.h"
#include "core/Solver.h"
#include "aig/gia/gia.h"

using namespace std;

namespace avy
{

class MinisatItpSeq : public ::Minisat::ProofVisitor
{
public:
    MinisatItpSeq(::Minisat::Solver& s, int numOfVars, const vector<int>& vars2vars, unsigned size) :
          ::Minisat::ProofVisitor()
        , m_Solver(s)
        , m_NumOfVars(numOfVars)
        , m_VarToModelVarId(vars2vars)
        , seqSize(size)
        , clauseToItp(size)
        , itpForVar(size)
    {
        m_pMan = Gia_ManStart(numOfVars);
        Gia_ManHashStart(m_pMan);
        for (unsigned i=0; i < numOfVars; i++)
            Gia_ManAppendCi(m_pMan);

        for (int i=0; i < seqSize; i++)
        	itpForVar[i].growTo(s.nVars(),-1);
    }

    ~MinisatItpSeq()
    {
    	Gia_ManHashStop(m_pMan);
    	Gia_ManStop(m_pMan);
    }

    Gia_Man_t* getInterpolantMan() { return m_pMan; }

    void visitLeaf(::Minisat::CRef cls, const ::Minisat::Clause& c)
    {
    	::Minisat::Var v = var(c[0]);
        for (int part = 1; part <= seqSize; part++)
        {
        	int label = Gia_ManConst1Lit();
			const ::Minisat::Range& r = c.part();
			assert(r.min() == r.max());
			if (r.min() <= part)
				label = markLeaf(part, c);
            clauseToItp[part-1].insert(cls, label);
            if (c.size() == 1) itpForVar[part-1][v] = label;
        }
    }

    virtual int visitResolvent (::Minisat::Lit resolvent, ::Minisat::Lit p1, ::Minisat::CRef p2)
    {
    	::Minisat::Var v = ::Minisat::var(resolvent);
    	::Minisat::Var v1 = ::Minisat::var(p1);
		for (int part=1; part <= seqSize; part++)
		{
			::Minisat::vec<int>& itpVec = itpForVar[part-1];
			int label1, label2;
			assert(itpVec.size() > v1);
			label1 = itpVec[v1];
			if (label1 == -1) {
				::Minisat::CRef r = m_Solver.getReason(v1);
				const ::Minisat::Clause& c1 = m_Solver.getClause(r);
				assert(c1.part().min() == c1.part().max());
				assert(c1.size() == 1);
				visitLeaf(r, c1);
				label1 = itpVec[v1];
			}
			assert(label1 != -1);
			bool res = clauseToItp[part-1].has(p2, label2);
			if (res == false) {
				const ::Minisat::Clause& c2 = m_Solver.getClause(p2);
				assert(c2.part().min() == c2.part().max());
				visitLeaf(p2, c2);
				label2 = clauseToItp[part-1][p2];
			}

			int label = getLabelByPivot(v1, part, label1, label2);
			itpVec[v] = label;
		 }
		 return 0;
	 }

    virtual int visitChainResolvent (::Minisat::Lit parent)
    {
    	::Minisat::Var v = ::Minisat::var(parent);
    	::Minisat::CRef c = chainClauses[0];
        int size = chainPivots.size();
        assert(size > 0);
        for (int part=1; part <= seqSize; part++)
        {
        	int label;
			bool res = clauseToItp[part-1].has(c, label);
			if (res == false) {
				visitLeaf(c, m_Solver.getClause(c));
				label = clauseToItp[part-1][c];
			}
            ::Minisat::vec<int>& itpVec = itpForVar[part-1];
            for (int i = 0; i < size; i++)
            {
                ::Minisat::Var pivot = ::Minisat::var(chainPivots[i]);
                int l = itpVec[pivot];
                if (l == -1) {
                	::Minisat::CRef r = m_Solver.getReason(pivot);
                	const ::Minisat::Clause& pC = m_Solver.getClause(r);
					assert(pC.part().min() == pC.part().max());
                	assert(pC.size() == 1);
                	visitLeaf(r, pC);
                	l = itpVec[pivot];
                }
                assert(l != -1);
                label = getLabelByPivot(pivot, part, label, l);
            }

            itpVec[v] = label;
        }
        return 0;
    }

    virtual int visitChainResolvent (::Minisat::CRef parent)
    {
        assert(chainPivots.size() > 0);
        assert(chainClauses.size() > 0);
        assert(chainPivots.size() >= chainClauses.size() ||
        		chainPivots.size() == chainClauses.size() - 1);

        ::Minisat::CRef c = chainClauses[0];
        for (int part=1; part <= seqSize; part++)
        {
            ::Minisat::CMap<int>& clsToItp = clauseToItp[part-1];
            ::Minisat::vec<int>& itpVec = itpForVar[part-1];
            int label;
            bool res = clsToItp.has(c, label);
            if (res == false) {
            	const ::Minisat::Clause& cls = m_Solver.getClause(c);
				assert(cls.part().min() == cls.part().max());
				visitLeaf(c, cls);
				label = clauseToItp[part-1][c];
			}

            int i = 0;
            int size = chainClauses.size();
            for (; i < size-1; i++)
            {
                ::Minisat::Var pivot = ::Minisat::var(chainPivots[i]);
                int l;
                ::Minisat::CRef r = chainClauses[i+1];
                res = clsToItp.has(r, l);
                if (res == false) {
                	const ::Minisat::Clause& cls = m_Solver.getClause(r);
					assert(cls.part().min() == cls.part().max());
					visitLeaf(r, cls);
					l = clauseToItp[part-1][r];
				}
                label = getLabelByPivot(pivot, part, label, l);
            }
            size = chainPivots.size();
            for (; i < size; i++)
            {
            	::Minisat::Var pivot = ::Minisat::var(chainPivots[i]);
            	assert(itpVec.size() > pivot);
				int l = itpVec[pivot];
				if (l == -1) {
					::Minisat::CRef r = m_Solver.getReason(pivot);
					const ::Minisat::Clause& cls = m_Solver.getClause(r);
					assert(cls.part().min() == cls.part().max());
					assert(cls.size() == 1);
					visitLeaf(r, cls);
					l = itpVec[pivot];
				}
				assert(l != -1);
				label = getLabelByPivot(pivot, part, label, l);
            }

            if (parent != ::Minisat::CRef_Undef) {
            	clsToItp.insert(parent, label);
            	const ::Minisat::Clause& cP = m_Solver.getClause(parent);
            	if (cP.size() == 1) itpForVar[part-1][var(cP[0])] = label;
            }
            else
            	Gia_ManAppendCo(m_pMan, label);
        }
        return 0;

    }

private:
    int markLeaf(int part, const ::Minisat::Clause& c)
    {
        Gia_Obj_t* pLabel = Gia_ManConst0(m_pMan);
        int label = Gia_ObjToLit(m_pMan, pLabel);
        for (int i=0; i < c.size(); i++)
        {
            ::Minisat::Var x = ::Minisat::var(c[i]);
            ::Minisat::Range r = m_Solver.getVarRange(x);
            if (r.min() == part && r.max() > part)
            {
            	assert(r.min() <= r.max() + 1 && r.min() >= r.max() - 1);
            	//cout << "(min,max): (" << r.min() << "," << r.max() << ")\n";
            	assert(m_VarToModelVarId.size() > x);
				int varId = m_VarToModelVarId[x];
				assert(varId >= 0 && varId < m_NumOfVars);

				Gia_Obj_t* pLeaf = Gia_ManCi(m_pMan, varId);
				if (::Minisat::sign(c[i]))
					pLeaf = Gia_Not(pLeaf);

				label = Gia_ManHashOr(m_pMan, label, Gia_ObjToLit(m_pMan, pLeaf));
				pLabel = Gia_Lit2Obj(m_pMan, label);
            }
        }

        return label;
    }

    int getLabelByPivot(::Minisat::Var pivot, int part, int label1, int label2)
    {
        ::Minisat::Range r = m_Solver.getVarRange(pivot);
        if (label1 == label2 && label1 == Gia_ManConst0Lit()) return Gia_ManConst0Lit();
        if (label1 == label2 && label1 == Gia_ManConst1Lit()) return Gia_ManConst1Lit();
        if (label1 == label2) return label1;
        if (r.min() <= part && r.max() <= part) // -- Interpolation for (A,B) pair - partition 1 = localA
			return Gia_ManHashOr(m_pMan, label1, label2);

        return Gia_ManHashAnd(m_pMan, label1, label2);
    }

private:
    const ::Minisat::Solver&               m_Solver;           // -- The SAT instance
    Gia_Man_t*                             m_pMan;             // -- Manager for the interpolant
    int                                    m_NumOfVars;
    const vector<int>&                     m_VarToModelVarId;

    unsigned int                           seqSize;            // -- ItpSeq size, always greater than 0.
    ::Minisat::vec< ::Minisat::vec<int> >  itpForVar;          // -- Itp labeling on the trail
    ::Minisat::vec< ::Minisat::CMap<int> > clauseToItp;        // -- Clause to its Itp labeling
};

}

#endif /* MINISAT_ITP_SEQ_H_ */

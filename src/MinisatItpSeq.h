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
          ::Minisat::ProofVisitor(size)
        , m_Solver(s)
        , m_NumOfVars(numOfVars)
        , m_VarToModelVarId(vars2vars)
    {
        m_pMan = Gia_ManStart(numOfVars);
        for (unsigned i=0; i < numOfVars; i++)
            Gia_ManAppendCi(m_pMan);

        for (int i=0; i < seqSize; i++)
        	itpForVar[i].growTo(s.nVars(),-1);
    }

    Gia_Man_t* getInterpolantMan() { return m_pMan; }

    virtual int visitLeaf(::Minisat::Var v, ::Minisat::CRef c, const ::Minisat::vec< ::Minisat::Lit>& lits)
    {
        for (int part = 1; part <= seqSize; part++)
        {
            int label = markLeaf(part, lits);
            itpForVar[part-1][v] = label;
            clauseToItp[part-1].insert(c,label);
        }
        return 0;
    }

    virtual int visitLeaf(::Minisat::CRef cls, const ::Minisat::vec< ::Minisat::Lit>& lits)
    {
        for (int part = 1; part <= seqSize; part++)
        {
            int label = markLeaf(part, lits);
            clauseToItp[part-1].insert(cls, label);
        }
        return 0;
    }

    virtual int visitResolvent (::Minisat::CRef parent, ::Minisat::Var resolvent, ::Minisat::CRef p1, ::Minisat::CRef p2)
    {
        for (int part=1; part <= seqSize; part++)
        {
            ::Minisat::CMap<int>& clsToItp = clauseToItp[part-1];
            int label1, label2;
            assert(clsToItp.has(p1, label1));
            assert(clsToItp.has(p2, label2));

            int label = getLabelByPivot(resolvent, part, label1, label2);
            clsToItp.insert(parent, label);
        }
        return 0;
    }

    virtual int visitResolvent (::Minisat::Var resolvent, ::Minisat::Var p1, ::Minisat::CRef p2)
    {
        for (int part=1; part <= seqSize; part++)
        {
            ::Minisat::vec<int>& itpVec = itpForVar[part-1];
            int label1, label2;
            assert(itpVec.size() > p1);
            label1 = itpVec[p1];
            assert(label1 != -1);
            assert(clauseToItp[part-1].has(p2, label2));

            int label = getLabelByPivot(resolvent, part, label1, label2);
            if (itpVec.size() <= resolvent)
                itpVec.growTo(resolvent+1);
            itpVec[resolvent] = label;
        }
        return 0;
    }

    virtual int visitHyperResolvent (::Minisat::Var parent)
    {
    	::Minisat::CRef c = hyperClauses[0];
        int size = hyperChildren.size();
        assert(size > 0);
        for (int part=1; part <= seqSize; part++)
        {
        	int label;
			bool res = clauseToItp[part-1].has(c, label);
			assert(res == true);
            ::Minisat::vec<int>& itpVec = itpForVar[part-1];
            for (int i = 0; i < size; i++)
            {
                ::Minisat::Var pivot = hyperChildren[i];
                assert(itpVec.size() > pivot);
                int l = itpVec[pivot];
                assert(l != -1);
                label = getLabelByPivot(pivot, part, label, l);
            }

            if (itpVec.size() <= parent) itpVec.growTo(parent+1,-1);
            itpVec[parent] = label;
        }
        return 0;
    }

    virtual int visitHyperResolvent (::Minisat::CRef parent)
    {
        assert(hyperChildren.size() > 0);
        assert(hyperClauses.size() > 0);
        assert(hyperChildren.size() >= hyperClauses.size() ||
        		hyperChildren.size() == hyperClauses.size() - 1);

        ::Minisat::CRef c = hyperClauses[0];
        int size = hyperClauses.size();
        for (int part=1; part <= seqSize; part++)
        {
            ::Minisat::CMap<int>& clsToItp = clauseToItp[part-1];
            ::Minisat::vec<int>& itpVec = itpForVar[part-1];
            int label;
            bool res = clsToItp.has(c, label);
            assert(res == true);

            int i = 0;
            for (; i < size-1; i++)
            {
                ::Minisat::Var pivot = hyperChildren[i];
                int l;
                res = clsToItp.has(hyperClauses[i+1], l);
                assert(res == true);
                label = getLabelByPivot(pivot, part, label, l);
            }
            size = hyperChildren.size();
            for (; i < size; i++)
            {
            	::Minisat::Var pivot = hyperChildren[i];
            	assert(itpVec.size() > pivot);
				int l = itpVec[pivot];
				assert(l != -1);
				label = getLabelByPivot(pivot, part, label, l);
            }

            if (parent != ::Minisat::CRef_Undef)
            	clsToItp.insert(parent, label);
            else
            	Gia_ManAppendCo(m_pMan, label);
        }
        return 0;

    }

    virtual bool itpExists(::Minisat::CRef c)
    {
        for (int part=1; part <= seqSize; part++)
        {
            ::Minisat::CMap<int>& clsToItp = clauseToItp[part-1];
            int x;
            if (clsToItp.has(c, x) == false)
                return false;
        }
        return true;
    }


private:
    int markLeaf(int part, const ::Minisat::vec< ::Minisat::Lit>& lits)
    {
        Gia_Obj_t* pLabel = Gia_ManConst0(m_pMan);
        int label = Gia_ObjToLit(m_pMan, pLabel);
        for (int i=0; i < lits.size(); i++)
        {
            ::Minisat::Var x = ::Minisat::var(lits[i]);
            ::Minisat::Range r = m_Solver.getVarRange(x);
            if (r.min() == part && r.max() > part)
            {
            	assert(r.min() <= r.max() + 1 && r.min() >= r.max() - 1);
            	//cout << "(min,max): (" << r.min() << "," << r.max() << ")\n";
            	assert(m_VarToModelVarId.size() > x);
				int varId = m_VarToModelVarId[x];
				assert(varId >= 0 && varId < m_NumOfVars);

				Gia_Obj_t* pLeaf = Gia_ManCi(m_pMan, varId);
				if (::Minisat::sign(lits[i]))
					pLeaf = Gia_Not(pLeaf);

				label = Gia_ManAppendOr(m_pMan, label, Gia_ObjToLit(m_pMan, pLeaf));
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
        	if (label1 == Gia_ManConst1Lit() || label2 == Gia_ManConst1Lit())
        		return Gia_ManConst1Lit();
        	else if (label1 == Gia_ManConst0Lit() || label2 == Gia_ManConst0Lit())
        		return (label1 == Gia_ManConst0Lit()) ? label2 : label1;
        	else if (label1 == Abc_LitNot(label2))
        		return Gia_ManConst1Lit();
        	else
        		return Gia_ManAppendOr(m_pMan, label1, label2);

        if (label1 == Gia_ManConst0Lit() || label2 == Gia_ManConst0Lit())
        	return Gia_ManConst0Lit();
        else if (label1 == Gia_ManConst1Lit() || label2 == Gia_ManConst1Lit())
        	return (label1 == Gia_ManConst1Lit()) ? label2 : label1;
        else if (label1 == Abc_LitNot(label2))
			return Gia_ManConst0Lit();
        return Gia_ManAppendAnd(m_pMan, label1, label2);
    }

private:
    const ::Minisat::Solver&    m_Solver;           // -- The SAT instance
    Gia_Man_t*                  m_pMan;             // -- Manager for the interpolant
    int                         m_NumOfVars;
    const vector<int>&          m_VarToModelVarId;
};

}

#endif /* MINISAT_ITP_SEQ_H_ */

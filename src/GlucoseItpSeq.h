/*
 * MinisatItpSeq.h
 *
 *  Created on: Jan 20, 2014
 *      Author: yakir
 */

#ifndef GLUCOSE_ITP_SEQ_H_
#define GLUCOSE_ITP_SEQ_H_

#include <vector>
#include "glucose/core/ProofVisitor.h"
#include "glucose/core/Solver.h"
#include "aig/gia/gia.h"

using namespace std;

namespace avy
{

class GlucoseItpSeq : public ::Glucose::ProofVisitor
{
public:
    GlucoseItpSeq(::Glucose::Solver& s, int numOfVars, const vector<int>& vars2vars, unsigned size) :
          ::Glucose::ProofVisitor(size)
        , m_Solver(s)
        , m_NumOfVars(numOfVars)
        , m_VarToModelVarId(vars2vars)
    {
        m_pMan = Gia_ManStart(numOfVars);
        Gia_ManHashStart(m_pMan);
        for (unsigned i=0; i < numOfVars; i++)
            Gia_ManAppendCi(m_pMan);

        for (int i=0; i < seqSize; i++)
        	itpForVar[i].growTo(s.nVars(),-1);
    }

    ~GlucoseItpSeq()
    {
    	Gia_ManHashStop(m_pMan);
    	Gia_ManStop(m_pMan);
    }

    Gia_Man_t* getInterpolantMan() { return m_pMan; }

    virtual int visitLeaf(::Glucose::Var v, ::Glucose::CRef c, const ::Glucose::vec< ::Glucose::Lit>& lits)
    {
        for (int part = 1; part <= seqSize; part++)
        {
            int label = Gia_ManConst1Lit();
            const ::Glucose::Range& r = m_Solver.getClsRange(c);
            assert(r.min() == r.max());
            if (r.min() <= part)
            	label = markLeaf(part, lits);
            itpForVar[part-1][v] = label;
            clauseToItp[part-1].insert(c,label);
        }
        return 0;
    }

    virtual int visitLeaf(::Glucose::CRef cls, const ::Glucose::vec< ::Glucose::Lit>& lits)
    {
        for (int part = 1; part <= seqSize; part++)
        {
        	int label = Gia_ManConst1Lit();
			const ::Glucose::Range& r = m_Solver.getClsRange(cls);
			assert(r.min() == r.max());
			if (r.min() <= part)
				label = markLeaf(part, lits);
            clauseToItp[part-1].insert(cls, label);
        }
        return 0;
    }

    virtual int visitResolvent (::Glucose::CRef parent, ::Glucose::Var resolvent, ::Glucose::CRef p1, ::Glucose::CRef p2)
    {
        for (int part=1; part <= seqSize; part++)
        {
            ::Glucose::CMap<int>& clsToItp = clauseToItp[part-1];
            int label1, label2;
            bool res = clsToItp.has(p1, label1);
            assert(res == true);
            res = clsToItp.has(p2, label2);
            assert(res == true);

            int label = getLabelByPivot(resolvent, part, label1, label2);
            clsToItp.insert(parent, label);
        }
        return 0;
    }

    virtual int visitResolvent (::Glucose::Var resolvent, ::Glucose::Var p1, ::Glucose::CRef p2)
    {
        for (int part=1; part <= seqSize; part++)
        {
            ::Glucose::vec<int>& itpVec = itpForVar[part-1];
            int label1, label2;
            assert(itpVec.size() > p1);
            label1 = itpVec[p1];
            assert(label1 != -1);
            bool res = clauseToItp[part-1].has(p2, label2);
            assert(res == true);

            int label = getLabelByPivot(p1, part, label1, label2);
            if (itpVec.size() <= resolvent)
                itpVec.growTo(resolvent+1);
            itpVec[resolvent] = label;
        }
        return 0;
    }

    virtual int visitHyperResolvent (::Glucose::Var parent)
    {
    	::Glucose::CRef c = hyperClauses[0];
        int size = hyperChildren.size();
        assert(size > 0);
        for (int part=1; part <= seqSize; part++)
        {
        	int label;
			bool res = clauseToItp[part-1].has(c, label);
			assert(res == true);
            ::Glucose::vec<int>& itpVec = itpForVar[part-1];
            for (int i = 0; i < size; i++)
            {
                ::Glucose::Var pivot = hyperChildren[i];
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

    virtual int visitHyperResolvent (::Glucose::CRef parent)
    {
        assert(hyperChildren.size() > 0);
        assert(hyperClauses.size() > 0);
        assert(hyperChildren.size() >= hyperClauses.size() ||
        		hyperChildren.size() == hyperClauses.size() - 1);

        ::Glucose::CRef c = hyperClauses[0];
        for (int part=1; part <= seqSize; part++)
        {
            ::Glucose::CMap<int>& clsToItp = clauseToItp[part-1];
            ::Glucose::vec<int>& itpVec = itpForVar[part-1];
            int label;
            bool res = clsToItp.has(c, label);
            assert(res == true);

            int i = 0;
            int size = hyperClauses.size();
            for (; i < size-1; i++)
            {
                ::Glucose::Var pivot = hyperChildren[i];
                int l;
                res = clsToItp.has(hyperClauses[i+1], l);
                assert(res == true);
                label = getLabelByPivot(pivot, part, label, l);
            }
            size = hyperChildren.size();
            for (; i < size; i++)
            {
            	::Glucose::Var pivot = hyperChildren[i];
            	assert(itpVec.size() > pivot);
				int l = itpVec[pivot];
				assert(l != -1);
				label = getLabelByPivot(pivot, part, label, l);
            }

            if (parent != ::Glucose::CRef_Undef)
            	clsToItp.insert(parent, label);
            else
            	Gia_ManAppendCo(m_pMan, label);
        }
        return 0;

    }

    virtual bool itpExists(::Glucose::CRef c)
    {
        for (int part=1; part <= seqSize; part++)
        {
            ::Glucose::CMap<int>& clsToItp = clauseToItp[part-1];
            int x;
            if (clsToItp.has(c, x) == false)
                return false;
        }
        return true;
    }


private:
    int markLeaf(int part, const ::Glucose::vec< ::Glucose::Lit>& lits)
    {
        Gia_Obj_t* pLabel = Gia_ManConst0(m_pMan);
        int label = Gia_ObjToLit(m_pMan, pLabel);
        for (int i=0; i < lits.size(); i++)
        {
            ::Glucose::Var x = ::Glucose::var(lits[i]);
            ::Glucose::Range r = m_Solver.getVarRange(x);
            if (r.min() == part && r.max() > part)
            {
            	assert(r.min() <= r.max() + 1 && r.min() >= r.max() - 1);
            	//cout << "(min,max): (" << r.min() << "," << r.max() << ")\n";
            	assert(m_VarToModelVarId.size() > x);
				int varId = m_VarToModelVarId[x];
				assert(varId >= 0 && varId < m_NumOfVars);

				Gia_Obj_t* pLeaf = Gia_ManCi(m_pMan, varId);
				if (::Glucose::sign(lits[i]))
					pLeaf = Gia_Not(pLeaf);

				label = Gia_ManHashOr(m_pMan, label, Gia_ObjToLit(m_pMan, pLeaf));
				pLabel = Gia_Lit2Obj(m_pMan, label);
            }
        }

        return label;
    }

    int getLabelByPivot(::Glucose::Var pivot, int part, int label1, int label2)
    {
        ::Glucose::Range r = m_Solver.getVarRange(pivot);
        if (label1 == label2 && label1 == Gia_ManConst0Lit()) return Gia_ManConst0Lit();
        if (label1 == label2 && label1 == Gia_ManConst1Lit()) return Gia_ManConst1Lit();
        if (label1 == label2) return label1;
        if (r.min() <= part && r.max() <= part) // -- Interpolation for (A,B) pair - partition 1 = localA
			return Gia_ManHashOr(m_pMan, label1, label2);

        return Gia_ManHashAnd(m_pMan, label1, label2);
    }

private:
    const ::Glucose::Solver&    m_Solver;           // -- The SAT instance
    Gia_Man_t*                  m_pMan;             // -- Manager for the interpolant
    int                         m_NumOfVars;
    const vector<int>&          m_VarToModelVarId;
};

}

#endif /* GLUCOSE_ITP_SEQ_H_ */

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
    }

    Gia_Man_t* getInterpolantMan() { return m_pMan; }

    virtual int visitLeaf(::Minisat::Var v, const ::Minisat::vec< ::Minisat::Lit>& lits)
    {
        for (int part = 1; part <= seqSize; part++)
        {
            int label = markLeaf(part, lits);
            itpForVar[part-1][v] = label;
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
        int size = hyperChildren.size();
        assert(size > 0);
        for (int part=1; part <= seqSize; part++)
        {
            ::Minisat::vec<int>& itpVec = itpForVar[part-1];
            int label = itpVec[parent];
            for (int i = 0; i < size; i++)
            {
                ::Minisat::Var pivot = hyperChildren[i];
                int l = itpVec[pivot];
                label = getLabelByPivot(pivot, part, label, l);
            }

            itpVec[parent] = label;
        }
        return 0;
    }

    virtual int visitHyperResolvent (::Minisat::CRef parent)
    {
        assert(hyperChildren.size() > 0);
        assert(hyperClauses.size() > 0);
        assert(hyperChildren.size() == hyperClauses.size());

        int size = hyperClauses.size();
        for (int part=1; part <= seqSize; part++)
        {
            ::Minisat::CMap<int>& clsToItp = clauseToItp[part-1];
            int label;
            bool res = clsToItp.has(parent, label);
            assert(res == true);

            for (int i = 0; i < size; i++)
            {
                ::Minisat::Var pivot = hyperChildren[i];
                int l;
                res = clsToItp.has(hyperClauses[i], l);
                assert(res == true);
                label = getLabelByPivot(pivot, part, label, l);
            }

            clsToItp.insert(parent, label);
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
            if (r.min() == part && r.max() == part) continue;
            assert(r.min() == r.max() + 1 || r.min() == r.max() - 1);
            int varId = m_VarToModelVarId[x];
            assert(varId >= 0 && varId < m_NumOfVars);

            Gia_Obj_t* pLeaf = Gia_ManCi(m_pMan, varId);
            if (::Minisat::sign(lits[i]))
                pLeaf = Gia_Not(pLeaf);

            label = Gia_ManAppendOr(m_pMan, label, Gia_ObjToLit(m_pMan, pLeaf));
            pLabel = Gia_Lit2Obj(m_pMan, label);
        }

        return label;
    }

    int getLabelByPivot(::Minisat::Var pivot, int part, int label1, int label2)
    {
        ::Minisat::Range r = m_Solver.getVarRange(pivot);
        if (r.min() <= part && r.max() <= part) // -- Interpolation for (A,B) pair - partition 1 = localA
            return Gia_ManAppendOr(m_pMan, label1, label2);
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

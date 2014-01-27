/*
 * MinisatInterpolation.h
 *
 *  Created on: Jan 20, 2014
 *      Author: yakir
 */

#ifndef MINISAT_INTERPOLATION_H_
#define MINISAT_INTERPOLATION_H_

#include <vector>
#include "core/ProofVisitor.h"
#include "core/Solver.h"
#include "aig/gia/gia.h"

using namespace std;

namespace avy
{

class MinisatInterpolation : public ::Minisat::ProofVisitor
{
public:
    virtual int visitLeaf(::Minisat::Var v, const ::Minisat::vec< ::Minisat::Lit>& lits)
    {
        int label = markLeaf(lits);
        itpForVar[v] = label;
        return label;
    }

    virtual int visitLeaf(::Minisat::CRef cls, const ::Minisat::vec< ::Minisat::Lit>& lits)
    {
        int label = markLeaf(lits);
        clauseToItp.insert(cls, label);
        return label;
    }

    virtual int visitResolvent (::Minisat::CRef parent, ::Minisat::Var resolvent, ::Minisat::CRef p1, ::Minisat::CRef p2)
    {
        int label1, label2;
        assert(clauseToItp.has(p1, label1));
        assert(clauseToItp.has(p2, label2));

        int label = getLabelByPivot(resolvent, label1, label2);
        clauseToItp.insert(parent, label);
        return label;
    }

    virtual int visitResolvent (::Minisat::Var resolvent, ::Minisat::Var p1, ::Minisat::CRef p2)
    {
        int label1, label2;
        assert(itpForVar.size() > p1);
        label1 = itpForVar[p1];
        assert(clauseToItp.has(p2, label2));

        int label = getLabelByPivot(resolvent, label1, label2);
        if (itpForVar.size() <= resolvent)
            itpForVar.growTo(resolvent+1);
        itpForVar[resolvent] = label;
        return label;
    }

    virtual int visitHyperResolvent (::Minisat::Var parent)
    {
        int size = hyperChildren.size();
        assert(size > 0);
        int label = itpForVar[parent];
        for (int i = 0; i < size; i++)
        {
            ::Minisat::Var pivot = hyperChildren[i];
            int l = itpForVar[pivot];
            label = getLabelByPivot(pivot, label, l);
        }

        itpForVar[parent] = label;

        return label;
    }

    virtual int visitHyperResolvent (::Minisat::CRef parent)
    {
        assert(hyperChildren.size() > 0);
        assert(hyperClauses.size() > 0);
        assert(hyperChildren.size() == hyperClauses.size());

        int label;
        bool res = clauseToItp.has(parent, label);
        assert(res == true);

        int size = hyperClauses.size();
        for (int i = 0; i < size; i++)
        {
            ::Minisat::Var pivot = hyperChildren[i];
            int l;
            res = clauseToItp.has(hyperClauses[i], l);
            assert(res == true);
            label = getLabelByPivot(pivot, label, l);
        }

        clauseToItp.insert(parent, label);
        return label;

    }

private:
    int markLeaf(const ::Minisat::vec< ::Minisat::Lit>& lits)
    {
        Gia_Obj_t* pLabel = Gia_ManConst0(m_pMan);
        int label = Gia_ObjToLit(m_pMan, pLabel);
        for (int i=0; i < lits.size(); i++)
        {
            ::Minisat::Var x = ::Minisat::var(lits[i]);
            Gia_Obj_t* pLeaf = m_LeafToObj[x];
            if (pLeaf == NULL) {
                 pLeaf = Gia_ManAppendObj(m_pMan);
                m_LeafToObj[x] = pLeaf;
            }

            if (::Minisat::sign(lits[i]))
                pLeaf = Gia_Not(pLeaf);

            label = Gia_ManAppendOr(m_pMan, label, Gia_ObjToLit(m_pMan, pLeaf));
            pLabel = Gia_Lit2Obj(m_pMan, label);
        }

        return label;
    }

    int getLabelByPivot(::Minisat::Var pivot, int label1, int label2)
    {
        ::Minisat::Range r = m_Solver.getVarRange(pivot);
        if (r.min() == 1 && r.max() == 1) // -- Interpolation for (A,B) pair - partition 1 = localA
            return Gia_ManAppendOr(m_pMan, label1, label2);
        return Gia_ManAppendAnd(m_pMan, label1, label2);
    }

private:
    const ::Minisat::Solver&    m_Solver;       // -- The SAT instance
    Gia_Man_t*                  m_pMan;         // -- Manager for the interpolant
    vector<Gia_Obj_t*>          m_LeafToObj;    // -- A map from a Var to an Obj in Gia
};

}

#endif /* MINISAT_INTERPOLATION_H_ */

/*
 * BMCSolver.cc
 *
 *  Created on: Jul 25, 2013
 *      Author: yakir
 */

#include <stdio.h>
#include <assert.h>
#include <iostream>

#include "BMCSolver.h"
#include "base/main/main.h"
#include "aig/ioa/ioa.h"

using namespace abc;

#define DEBUG 0

BMCSolver::BMCSolver(Aig_Man_t* pAig) :
      m_pAig(pAig)
    , m_pSat(NULL)
    , m_iFramePrev(0)
    , m_nLastFrame(0)
    , m_ClausesByFrame(1)
    , m_VarsByFrame(1)
    , m_pBadStore (NULL)
    , m_pInitStore(NULL)
    , m_bTrivial(false)
    , m_bAddGlueRemovalLiteral(false)
    , m_nLevelRemoval(-1)
{
    m_pSat = sat_solver2_new();
    sat_solver2_setnvars( m_pSat, 5000);

    m_pOneTR = duplicateAigWithoutPOs(m_pAig);
    m_pOneTRCnf = Cnf_Derive(m_pOneTR, Aig_ManRegNum(m_pOneTR));
    createInitMan();
    createBadMan();
    m_pInitCnf = Cnf_Derive(m_pInit, 0);
    m_pBadCnf = Cnf_Derive(m_pBad, Aig_ManCoNum(m_pBad));
}

void BMCSolver::addTransitionsFromTo(unsigned nFrom, unsigned nTo)
{
	assert(nFrom >= 0 && nFrom == m_nLastFrame && nFrom < nTo);

    m_iFramePrev = m_nLastFrame;
    int nDelta = m_pInitCnf->nVars + 1 + (nFrom)*(m_pOneTRCnf->nVars + 1);// + m_pBadCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, nDelta);
    int nGlueVar = nDelta-1;

    for ( ; m_nLastFrame < nTo; m_nLastFrame++)
    {
        Aig_Obj_t *pObj;
        int i, Lits[3];
        Lits[2] = toLitCond(nGlueVar, 1);
        int nOffset = (m_bAddGlueRemovalLiteral && (m_nLevelRemoval == -1 || m_nLevelRemoval == m_nLastFrame)) ? 3 : 2;
        if (nFrom == 0)
        {
            Aig_ManForEachCi(m_pInit, pObj, i )
            {
                Aig_Obj_t *pObj2 = Saig_ManLo(m_pOneTR, i );

                int nVar = m_pOneTRCnf->pVarNums[pObj2->Id];

                Lits[0] = toLitCond(m_pInitCnf->pVarNums[pObj->Id], 0 );
                Lits[1] = toLitCond(nVar, 1 );
                addClauseToSat(Lits, Lits+nOffset, m_nLastFrame);

                Lits[0] = toLitCond(m_pInitCnf->pVarNums[pObj->Id], 1 );
                Lits[1] = toLitCond(nVar, 0 );
                addClauseToSat(Lits, Lits+nOffset, m_nLastFrame);
            }
        }
        else
        {
            Saig_ManForEachLo( m_pOneTR, pObj, i )
            {
                Aig_Obj_t *pObj2 = Saig_ManLi(m_pOneTR, i );

                int nVar = m_pOneTRCnf->pVarNums[pObj->Id]; // This is the global var.
                int nVar2 = m_pOneTRCnf->pVarNums[pObj2->Id] - m_pOneTRCnf->nVars - 1;// - m_pBadCnf->nVars;

                Lits[0] = toLitCond(nVar , 0 );
                Lits[1] = toLitCond(nVar2, 1 );
                addClauseToSat(Lits, Lits+nOffset, m_nLastFrame);

                Lits[0] = toLitCond(nVar , 1 );
                Lits[1] = toLitCond(nVar2, 0 );
                addClauseToSat(Lits, Lits+nOffset, m_nLastFrame);
            }
        }

        if (addCNFToSAT(m_pOneTRCnf, m_nLastFrame) == false)
            assert(false);

        markCnfVars(m_pOneTR, m_pOneTRCnf);

        Cnf_DataLift(m_pOneTRCnf, m_pOneTRCnf->nVars + 1);// + m_pBadCnf->nVars);
        nGlueVar += m_pOneTRCnf->nVars;
    }
#if DEBUG
    sat_solver2_store_write(m_pSat, "init_tr.cnf");
#endif
    Cnf_DataLift(m_pOneTRCnf, -nDelta - (nTo-nFrom)*(m_pOneTRCnf->nVars + 1));// + m_pBadCnf->nVars));
}

// ************************************************************************
// Collect the global variables for an unrolling of a BMC formula.
// ************************************************************************
void BMCSolver::prepareGlobalVars(int nFrame)
{
    int nDelta = m_pInitCnf->nVars + 1 + (nFrame-1)*(m_pOneTRCnf->nVars + 1);// + m_pBadCnf->nVars);

    m_GlobalVars.resize(nFrame);

    Aig_Obj_t *pObj;
    int i, Lits[2];
    Saig_ManForEachLi(m_pOneTR, pObj, i)
    {
        int nVar = m_pOneTRCnf->pVarNums[pObj->Id] + nDelta;
        m_GlobalVars[nFrame-1].push_back(nVar);
    }
}

bool BMCSolver::addCNFToSAT(Cnf_Dat_t *pCnf, unsigned nFrame)
{
    AVY_ASSERT (nFrame <= m_nLastFrame);

    for (int i = 0; i < pCnf->nClauses; i++)
    {
        if ( addClauseToSat(pCnf->pClauses[i], pCnf->pClauses[i+1], nFrame) == false)
        {
            return false;
        }
    }
    return true;
}

eResult BMCSolver::solveSat()
{
    Aig_Obj_t * pObj;
    int i, k, VarNum, Lit, RetValue;

    /*if ( m_pSat->qtail != m_pSat->qhead )
    {
        RetValue = sat_solver2_simplify(m_pSat);
        assert( RetValue != 0 );
    }*/

    //if ( m_nConfMaxAll && m_pSat->stats.conflicts > m_nConfMaxAll )
    //    return l_Undef;
    pObj = Aig_ManCo(m_pBad, 0);
# if DEBUG
    std::ostringstream os;
    os << "yakir_" << m_nLastFrame << ".cnf";
    const char* name = os.str().c_str();
    sat_solver2_store_write(m_pSat, (char*)name);
#endif
    //sat_solver2_bookmark(m_pSat);
    VarNum = m_pBadCnf->pVarNums[pObj->Id] + (m_pInitCnf->nVars + 1) + (m_nLastFrame - 1)*(m_pOneTRCnf->nVars + 1)/* + m_pBadCnf->nVars)*/ + m_pOneTRCnf->nVars;
    Lit = toLitCond( VarNum, Aig_IsComplement(pObj) ) ;
    /*if (addClauseToSat(&Lit, &Lit +1, m_nLastFrame) == false)
    {
        m_bTrivial = true;
        return FALSE;
    }*/
    RetValue = sat_solver2_solve( m_pSat, &Lit, &Lit + 1, (ABC_INT64_T)10000000, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    //RetValue = sat_solver2_solve( m_pSat, NULL,  NULL, (ABC_INT64_T)10000000, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

    if ( RetValue == l_False ) // unsat
    {
        // add final unit clause
#if 1
        Lit = lit_neg( Lit );
        addClauseToSat(&Lit, &Lit + 1, m_nLastFrame);
        // add learned units
        /*for ( k = 0; k < veci_size(&m_pSat->unit_lits); k++ )
        {
            Lit = veci_begin(&m_pSat->unit_lits)[k];
            status = sat_solver2_addclause( m_pSat, &Lit, &Lit + 1, 0 );
            assert( status );
        }
        veci_resize(&m_pSat->unit_lits, 0);*/
        // propagate units
        if (m_pSat->qtail != m_pSat->qhead )
        {
            int RetValue = sat_solver2_simplify(m_pSat);
            assert( RetValue != 0 );
            //sat_solver2_compress( m_pSat );
        }
#endif

        //sat_solver2_rollback(m_pSat);
        return FALSE;
    }
    if ( RetValue == l_Undef )
    {
        // undecided
        std::cout << "UNDEF!!\n";
        return UNDEF;
    }

    if (RetValue == l_True)
    {
        std::cout << "SAT!!\n";
    }

    // generate counter-example
    //m_pAig->pSeqModel = ??

    return TRUE;
}

// ************************************************************************
// Compute the interpolation sequence for the last BMC formula solved.
// ************************************************************************
Aig_Man_t* BMCSolver::getInterpolant()
{
    if (m_bTrivial == true)
    {
        assert(m_pAig->nRegs > 0);
        Aig_Man_t* pMan = Aig_ManStart(10000);
        Aig_IthVar(pMan, m_pAig->nRegs-1);
        Aig_ObjCreateCo(pMan, Aig_ManConst1(pMan));

        return pMan;
    }
}

Aig_Man_t* BMCSolver::duplicateAigWithoutPOs(Aig_Man_t* p)
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManRegNum(p) > 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi( p, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );
    // set registers
    pNew->nTruePis = p->nTruePis;
    pNew->nTruePos = Saig_ManConstrNum(p);
    pNew->nRegs    = p->nRegs;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );

    // create constraint outputs
    Saig_ManForEachPo( p, pObj, i )
    {
        if ( i < Saig_ManPoNum(p)-Saig_ManConstrNum(p) )
            continue;
        Aig_ObjCreateCo( pNew, Aig_Not( Aig_ObjChild0Copy(pObj) ) );
    }

    Saig_ManForEachLi( p, pObj, i )
        Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pNew );
    return pNew;
}

void BMCSolver::createInitMan()
{
    int i;
    int nRegs = Aig_ManRegNum(m_pAig);
    assert(nRegs > 0 );
    Aig_Obj_t ** ppInputs = ABC_ALLOC( Aig_Obj_t *, nRegs );
    m_pInit = Aig_ManStart( nRegs );
    for ( i = 0; i < nRegs; i++ )
        ppInputs[i] = Aig_Not( Aig_ObjCreateCi(m_pInit) );
    Aig_Obj_t *pRes = Aig_Multi( m_pInit, ppInputs, nRegs, AIG_OBJ_AND );
    Aig_ObjCreateCo(m_pInit, pRes );
    ABC_FREE( ppInputs );
}

void BMCSolver::createBadMan()
{
    // Only support one PO now.
    assert(Saig_ManPoNum(m_pAig) - Saig_ManConstrNum(m_pAig) == 1);
    assert(Saig_ManConstrNum(m_pAig) == 0);
    Aig_Obj_t * pObj = NULL;
    int i;
    assert( Aig_ManRegNum(m_pAig) > 0 );
    // create the new manager
    m_pBad = Aig_ManStart( Aig_ManObjNumMax(m_pAig) );
    m_pBad->pName = Abc_UtilStrsav(m_pAig->pName );
    m_pBad->pSpec = Abc_UtilStrsav(m_pAig->pSpec );

    // create the PIs
    Aig_ManCleanData(m_pAig);
    Aig_ManConst1(m_pAig)->pData = Aig_ManConst1(m_pBad);
    Aig_ManForEachCi(m_pAig, pObj, i )
        pObj->pData = Aig_ObjCreateCi( m_pBad );

    // set registers
    m_pBad->nRegs    = 0;
    m_pBad->nTruePis = Aig_ManCiNum(m_pAig);
    m_pBad->nTruePos = 1 + Saig_ManConstrNum(m_pAig);

    // duplicate internal nodes
    Aig_ManForEachNode(m_pAig, pObj, i )
        pObj->pData = Aig_And( m_pBad, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );

    // add the PO
    pObj = Aig_ManCo(m_pAig, 0 );
    Aig_ObjCreateCo(m_pBad, Aig_ObjChild0Copy(pObj) );

    // create constraint outputs
    Saig_ManForEachPo(m_pAig, pObj, i )
    {
        if ( i < Saig_ManPoNum(m_pAig)-Saig_ManConstrNum(m_pAig) )
            continue;
        Aig_ObjCreateCo( m_pBad, Aig_Not( Aig_ObjChild0Copy(pObj) ) );
    }

    Aig_ManCleanup(m_pBad);
}

Aig_Man_t* BMCSolver::createArbitraryCombMan(Aig_Man_t* pMan, int nOut)
{
    Aig_Obj_t * pObj = NULL;
    int i;

    assert(Aig_ManCiNum(pMan) == Saig_ManRegNum(m_pAig));

    // create the new manager
    Aig_Man_t* pNew = Aig_ManStart( Aig_ManObjNumMax(pMan) );
    pNew->pName = Abc_UtilStrsav(pMan->pName );
    pNew->pSpec = Abc_UtilStrsav(pMan->pSpec );

    // create the PIs
    Aig_ManCleanData(pMan);
    Aig_ManConst1(pMan)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi(pMan, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );

    // set registers
    pNew->nRegs    = 0;
    pNew->nTruePis = pMan->nTruePis;
    pNew->nTruePos = 1 ;

    // duplicate internal nodes
    Aig_ManForEachNode(pMan, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );

    // add the PO
    if (nOut >= 0)
    {
        pObj = Aig_ManCo(pMan, nOut );
        Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj) );
    }

    Aig_ManCleanup(pNew);

    return pNew;
}

bool BMCSolver::setInit()
{
    markCnfVars(m_pInit, m_pInitCnf);
    bool bRes = addCNFToSAT(m_pInitCnf, 0);
    //sat_solver2_store_write(m_pSat, "init.cnf");
    return bRes;
}

bool BMCSolver::setBad(int nFrame, bool bHasPIs)
{
    assert(nFrame > 0);
    int nDelta = m_pInitCnf->nVars + 1 +
                 (nFrame-1)*(m_pOneTRCnf->nVars + 1);// + m_pBadCnf->nVars);

    // Prepare CNF.
    Cnf_DataLift(m_pBadCnf, nDelta + m_pOneTRCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, nDelta);

    Aig_Obj_t* pObj;
    int i, Lits[3];
    int nGlueVar = nDelta - 1;
    Lits[2] = toLitCond(nGlueVar, 1);
    int nOffset = (m_bAddGlueRemovalLiteral && (m_nLevelRemoval == -1 || m_nLevelRemoval == m_nLastFrame)) ? 3 : 2;
    Saig_ManForEachLi(m_pOneTR, pObj, i)
    {
        assert ( i <= Aig_ManRegNum(m_pOneTR));
        Aig_Obj_t* pObj2 = Aig_ManCi(m_pBad, (bHasPIs) ? m_pOneTR->nTruePis+i : i );

        int nVar  = m_pOneTRCnf->pVarNums[pObj->Id];
        int nVar2 = m_pBadCnf->pVarNums[pObj2->Id]; // This is a global var

        //m_GlobalVars[m_nLastFrame].push_back(nVar2);

        Lits[0] = toLitCond(nVar , 0 );
        Lits[1] = toLitCond(nVar2, 1 );
        addClauseToSat(Lits, Lits+nOffset, nFrame);

        Lits[0] = toLitCond(nVar , 1 );
        Lits[1] = toLitCond(nVar2, 0 );
        addClauseToSat(Lits, Lits+nOffset, nFrame);
    }

    bool bRes = addCNFToSAT(m_pBadCnf, nFrame);
    markCnfVars(m_pBad, m_pBadCnf);

    // Revert CNF to its original state
    Cnf_DataLift(m_pBadCnf, -nDelta - m_pOneTRCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, -nDelta);

    assert(bRes);

    return bRes;
}

void BMCSolver::addClausesToFrame(Vec_Ptr_t* pCubes, unsigned nFrame)
{
    int nDelta = m_pInitCnf->nVars + 1 + (nFrame)*(m_pOneTRCnf->nVars + 1);// + (nFrame-1)*(m_pBadCnf->nVars);
    Pdr_Set_t* pCube;
    int i;

    Vec_PtrForEachEntry(Pdr_Set_t*, pCubes, pCube, i)
    {
        lit* pClause = ABC_ALLOC(lit, pCube->nTotal);
        int nCounter=0;
        for (int j=0; j < pCube->nTotal; j++)
        {
            if (pCube->Lits[j] == -1) continue;
            Aig_Obj_t *pObj = Saig_ManLo (m_pOneTR, lit_var (pCube->Lits [j]));
            assert(m_pOneTRCnf->pVarNums[pObj->Id] > 0);
            int nVar = m_pOneTRCnf->pVarNums[pObj->Id] + nDelta;
            int lit = toLitCond(nVar, 1 ^ lit_sign (pCube->Lits [j]));

            pClause[nCounter++] = lit;
        }

        bool bRes = addClauseToSat(pClause, pClause+nCounter, nFrame);
        assert(bRes);
        ABC_FREE(pClause);
    }
}


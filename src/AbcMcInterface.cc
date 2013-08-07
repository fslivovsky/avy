/*
 * AbcMcInterface.cc
 *
 *  Created on: Jul 25, 2013
 *      Author: yakir
 */

#include <stdio.h>
#include <assert.h>
#include <iostream>
#include <sstream>

#include "AbcMcInterface.h"
#include "base/main/main.h"
#include "aig/ioa/ioa.h"

using namespace abc;

#define DEBUG 0

//extern int Cmd_CommandExecute(void *pAbc, char *sCommand);

AbcMcInterface::AbcMcInterface(std::string strFileName) :
    m_iFramePrev(0)
    , m_nLastFrame(0)
{
    std::cout << "Setting up ABC.\n";
    Abc_Start();
    m_pAbcFramework = Abc_FrameGetGlobalFrame();

    char abcCommand[1000];
    sprintf(abcCommand, "read %s", strFileName.c_str());

    std::cout << "\tReading the AIG...\n";
    Cmd_CommandExecute(m_pAbcFramework, abcCommand);

    std::cout << "\tGetting the network from the ABC frame.\n";
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(m_pAbcFramework);
    m_pAig = Abc_NtkToDar(pNtk, 0, 1);

    std::cout << "\tSetup the SAT solver.\n";
    // create a SAT solver
    m_pSat         = sat_solver_new();
    //sat_solver_store_alloc( m_pSat ); STORE PROOF does not work. Sent Alan an email
    /*m_pSat->nLearntStart = 10000;
    m_pSat->nLearntDelta =  5000;
    m_pSat->nLearntRatio =    75;
    m_pSat->nLearntMax   = m_pSat->nLearntStart;*/
    sat_solver_setnvars( m_pSat, 2000 );

    m_pOneTR = duplicateAigWithoutPOs(m_pAig);
    m_pOneTRCnf = Cnf_Derive(m_pOneTR, Aig_ManRegNum(m_pOneTR));
    createInitMan();
    createBadMan();
    m_pInitCnf = Cnf_Derive(m_pInit, 0);
    Cnf_DataWriteIntoFile(m_pInitCnf, "init1.cnf", 0, NULL, NULL);
    m_pBadCnf = Cnf_Derive(m_pBad, Aig_ManCoNum(m_pBad));
    Cnf_DataWriteIntoFile(m_pBadCnf, "bad.cnf", 0, NULL, NULL);

    std::cout << m_pInitCnf->nVars << " " << m_pOneTRCnf->nVars << " " << m_pBadCnf->nVars << "\n";
    std::cout << "Done setting up ABC.\n";
}

void AbcMcInterface::addTransitionsFromTo(int nFrom, int nTo)
{
	assert(nFrom >= 0 && nFrom == m_nLastFrame && nFrom < nTo);

    m_iFramePrev = m_nLastFrame;
    int nDelta = m_pInitCnf->nVars + (nFrom)*(m_pOneTRCnf->nVars + m_pBadCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, nDelta);
    for ( ; m_nLastFrame < nTo; m_nLastFrame++)
    {
        Aig_Obj_t *pObj;
        int i, Lits[2];
        if (nFrom == 0)
        {
            Aig_ManForEachCi(m_pInit, pObj, i )
            {
                Aig_Obj_t *pObj2 = Saig_ManLo(m_pOneTR, i );

                Lits[0] = toLitCond(m_pInitCnf->pVarNums[pObj->Id], 0 );
                Lits[1] = toLitCond(m_pOneTRCnf->pVarNums[pObj2->Id], 1 );
                if ( !sat_solver_addclause(m_pSat, Lits, Lits+2 ) )
                    assert(false);
                Lits[0] = toLitCond(m_pInitCnf->pVarNums[pObj->Id], 1 );
                Lits[1] = toLitCond(m_pOneTRCnf->pVarNums[pObj2->Id], 0 );
                if ( !sat_solver_addclause(m_pSat, Lits, Lits+2 ) )
                    assert(false);
            }
        }
        else
        {
            Saig_ManForEachLo( m_pOneTR, pObj, i )
            {
                //Vec_IntPush( vVarsAB, pCnfFrames->pVarNums[pObj->Id] );

                Aig_Obj_t *pObj2 = Saig_ManLi(m_pOneTR, i );

                Lits[0] = toLitCond(m_pOneTRCnf->pVarNums[pObj->Id], 0 );
                Lits[1] = toLitCond(m_pOneTRCnf->pVarNums[pObj2->Id] - m_pOneTRCnf->nVars - m_pBadCnf->nVars, 1 );
                if ( !sat_solver_addclause(m_pSat, Lits, Lits+2 ) )
                {
#if DEBUG
                    sat_solver_store_write(m_pSat, "xxx.cnf");
#endif
                    assert(false);
                }

                Lits[0] = toLitCond(m_pOneTRCnf->pVarNums[pObj->Id], 1 );
                Lits[1] = toLitCond(m_pOneTRCnf->pVarNums[pObj2->Id] - m_pOneTRCnf->nVars - m_pBadCnf->nVars, 0 );
                if ( !sat_solver_addclause(m_pSat, Lits, Lits+2 ) )
                {
#if DEBUG
                    sat_solver_store_write(m_pSat, "xxx.cnf");
#endif
                    assert(false);
                }
            }
        }

        if (addCNFToSAT(m_pOneTRCnf) == false)
            assert(false);

        Cnf_DataLift(m_pOneTRCnf, m_pOneTRCnf->nVars + m_pBadCnf->nVars);
    }
#if DEBUG
    sat_solver_store_write(m_pSat, "init_tr.cnf");
#endif
    Cnf_DataLift(m_pOneTRCnf, -nDelta - (nTo-nFrom)*(m_pOneTRCnf->nVars + m_pBadCnf->nVars));
}

bool AbcMcInterface::addCNFToSAT(Cnf_Dat_t *pCnf)
{
    for (int i = 0; i < pCnf->nClauses; i++)
    {
        if ( !sat_solver_addclause(m_pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ))
        {
            return false;
        }
    }
    return true;
}

eResult AbcMcInterface::solveSat()
{
    Aig_Obj_t * pObj;
    int i, k, VarNum, Lit, status, RetValue;

    /*if ( m_pSat->qtail != m_pSat->qhead )
    {
        RetValue = sat_solver_simplify(m_pSat);
        assert( RetValue != 0 );
    }*/

    //if ( m_nConfMaxAll && m_pSat->stats.conflicts > m_nConfMaxAll )
    //    return l_Undef;
    pObj = Aig_ManCo(m_pBad, 0);
# if DEBUG
    std::ostringstream os;
    os << "yakir_" << m_nLastFrame << ".cnf";
    const char* name = os.str().c_str();
    sat_solver_store_write(m_pSat, (char*)name);
#endif
    VarNum = m_pBadCnf->pVarNums[pObj->Id] + (m_pInitCnf->nVars) + (m_nLastFrame - 1)*(m_pOneTRCnf->nVars + m_pBadCnf->nVars) + m_pOneTRCnf->nVars;
    Lit = toLitCond( VarNum, Aig_IsComplement(pObj) ) ;
    RetValue = sat_solver_solve( m_pSat, &Lit, &Lit + 1, (ABC_INT64_T)10000000, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

    if ( RetValue == l_False ) // unsat
    {
        // add final unit clause
        Lit = lit_neg( Lit );
        status = sat_solver_addclause( m_pSat, &Lit, &Lit + 1 );
        assert( status );
        // add learned units
        for ( k = 0; k < veci_size(&m_pSat->unit_lits); k++ )
        {
            Lit = veci_begin(&m_pSat->unit_lits)[k];
            status = sat_solver_addclause( m_pSat, &Lit, &Lit + 1 );
            assert( status );
        }
        veci_resize(&m_pSat->unit_lits, 0);
        // propagate units
        sat_solver_compress( m_pSat );
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

Aig_Man_t* AbcMcInterface::duplicateAigWithoutPOs(Aig_Man_t* p)
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

void AbcMcInterface::createInitMan()
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

void AbcMcInterface::createBadMan()
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

    /*
    // Map Const1
    Aig_ManConst1(m_pAig)->pData = Aig_ManConst1(m_pBad);
    // Traverse backwards untill the first PIs/LOs
    Aig_Obj_t* pRes = createCombSlice_rec(m_pBad, Aig_ObjFanin0(Aig_ManCo(m_pAig, 0)));

    // Create a single CO.
    Aig_ObjCreateCo(m_pBad, Aig_NotCond(pRes, Aig_ObjFaninC0(Aig_ManCo(m_pAig, 0))));

    // Now clean the Data field of the AIG.
    Aig_ManCleanData(m_pAig);*/
}

bool AbcMcInterface::setInit()
{
    bool bRes = addCNFToSAT(m_pInitCnf);
    sat_solver_store_write(m_pSat, "init.cnf");
    return bRes;
}

bool AbcMcInterface::setBad(int nFrame)
{
    assert(nFrame > 0);
    int nDelta = m_pInitCnf->nVars +
                 (nFrame-1)*(m_pOneTRCnf->nVars + m_pBadCnf->nVars);

    // Prepare CNF.
    Cnf_DataLift(m_pBadCnf, nDelta + m_pOneTRCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, nDelta);

    Aig_Obj_t* pObj;
    int i, Lits[2];
    Saig_ManForEachLi(m_pOneTR, pObj, i)
    {
        assert ( i <= Aig_ManRegNum(m_pOneTR));
        Aig_Obj_t* pObj2 = Aig_ManCi(m_pBad, m_pOneTR->nTruePis+i );

        Lits[0] = toLitCond(m_pOneTRCnf->pVarNums[pObj->Id], 0 );
        Lits[1] = toLitCond(m_pBadCnf->pVarNums[pObj2->Id], 1 );
        if ( !sat_solver_addclause(m_pSat, Lits, Lits+2 ) )
            assert(false);
        Lits[0] = toLitCond(m_pOneTRCnf->pVarNums[pObj->Id], 1 );
        Lits[1] = toLitCond(m_pBadCnf->pVarNums[pObj2->Id], 0 );
        if ( !sat_solver_addclause(m_pSat, Lits, Lits+2 ) )
            assert(false);
    }

    bool bRes = addCNFToSAT(m_pBadCnf);

    // Revert CNF to its original state
    Cnf_DataLift(m_pBadCnf, -nDelta - m_pOneTRCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, -nDelta);

    assert(bRes);

    return bRes;
}

Aig_Obj_t* AbcMcInterface::createCombSlice_rec(Aig_Man_t* pMan, Aig_Obj_t * pObj)
{
    Aig_Obj_t * pRes = (Aig_Obj_t*)(pObj->pData);
    if ( pRes != NULL )
        return pRes;

    // 1. For each PI and LO, simply create a CI.
    // 2. For each LO, CO or just a node, traverse backwards to create the logic.
    if ( Saig_ObjIsPi( m_pAig, pObj ) || Saig_ObjIsLo( m_pAig, pObj ))
        pRes = Aig_ObjCreateCi(pMan);
    else if ( Aig_ObjIsCo( pObj ) )
    {
        // Can this happen for comb slice?!
    }
    else
    {
        createCombSlice_rec(pMan, Aig_ObjFanin0(pObj));
        createCombSlice_rec(pMan, Aig_ObjFanin1(pObj));

        pRes = Aig_And( pMan, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    }
    assert( pRes != NULL );
    pObj->pData = pRes;
    return pRes;
}

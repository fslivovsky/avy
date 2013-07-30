/*
 * AbcMcInterface.cc
 *
 *  Created on: Jul 25, 2013
 *      Author: yakir
 */

#include <stdio.h>
#include <assert.h>
#include <iostream>

#include "AbcMcInterface.h"
#include "../abc/src/base/main/main.h"

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
    m_nObjs = Aig_ManObjNumMax(m_pAig);
    m_vAig2Frm = Vec_PtrAlloc( 100 );
    m_vObj2Var = Vec_IntAlloc( 0 );
    Vec_IntFill(m_vObj2Var, m_nObjs, 0 );

    std::cout << "\tSetup the unrolled model.\n";
    // start the AIG manager and map primary inputs
    m_pFrm = Aig_ManStart(m_nObjs);
    Aig_Obj_t * pObj;
    int i=0;
    Saig_ManForEachLo(m_pAig, pObj, i)
        setMappingForFrame(pObj, 0, Aig_ManConst0(m_pFrm) );

    std::cout << "\tSetup the SAT solver.\n";
    // create a SAT solver
    m_nSatVars     = 1;
    m_pSat         = sat_solver_new();
    m_pSat->nLearntStart = 10000;
    m_pSat->nLearntDelta =  5000;
    m_pSat->nLearntRatio =    75;
    m_pSat->nLearntMax   = m_pSat->nLearntStart;
    sat_solver_setnvars( m_pSat, 2000 );
    int Lit = toLit( m_nSatVars );

    // Add a redundant clause (True).
    sat_solver_addclause( m_pSat, &Lit, &Lit + 1 );

    // Map the constant True from the unrolled model to the SAT solver.
    setSatMapping(Aig_ManConst1(m_pFrm), m_nSatVars++ );

    // other data structures
    m_vVisited = Vec_IntAlloc( 1000 );
    m_vTargets     = Vec_PtrAlloc( 1000 );
    std::cout << "Done setting up ABC.\n";
}

void AbcMcInterface::addTransitionsFromTo(int nFrom, int nTo)
{
	assert(nFrom >= 0 && nFrom == m_nLastFrame && nFrom < nTo);

    Vec_PtrClear( m_vTargets );
    m_iFramePrev = m_nLastFrame;
    for ( ; m_nLastFrame < nTo; m_nLastFrame++)
    {
        // Map the node TRUE.
        setMappingForFrame(Aig_ManConst1(m_pAig), m_nLastFrame, Aig_ManConst1(m_pFrm));

        Vec_IntClear( m_vVisited );
        // Recursively construct the logic starting from the property.
        Aig_Obj_t* pTarget = constructFrameFromOutput_rec(Aig_ManCo(m_pAig, 0), m_nLastFrame, m_vVisited );
        Vec_PtrPush( m_vTargets, pTarget );
        Aig_ObjCreateCo( m_pFrm, pTarget );
        Aig_ManCleanup( m_pFrm ); // it is not efficient to cleanup the whole manager!!!

        // check if the node is gone
        int iFrame, i, iObj;
        Vec_IntForEachEntryDouble( m_vVisited, iObj, iFrame, i )
            getObjForFrame(Aig_ManObj(m_pAig, iObj), iFrame );
        // it is not efficient to remove nodes, which may be used later!!!
    }
}

void AbcMcInterface::updateSATSolverWithCNF(Cnf_Dat_t *pCnf)
{
    Aig_Obj_t *pObj;
    int i, Lits[2], VarNumOld, VarNumNew;
    Aig_ManForEachObjVec(m_vVisited, m_pFrm, pObj, i )
    {
        // get the new variable of this node
        Aig_Obj_t *pObjNew = (Aig_Obj_t *)pObj->pData;
        pObj->pData = NULL;
        VarNumNew = pCnf->pVarNums[ pObjNew->Id ];
        if ( VarNumNew == -1 )
            continue;
        // get the old variable of this node
        VarNumOld = getSatNum(pObj);
        if ( VarNumOld == 0 )
        {
            setSatMapping(pObj, VarNumNew);
            continue;
        }
        // add clauses connecting existing variables
        Lits[0] = toLitCond( VarNumOld, 0 );
        Lits[1] = toLitCond( VarNumNew, 1 );
        if ( !sat_solver_addclause( m_pSat, Lits, Lits+2 ) )
            assert( 0 );
        Lits[0] = toLitCond( VarNumOld, 1 );
        Lits[1] = toLitCond( VarNumNew, 0 );
        if ( !sat_solver_addclause( m_pSat, Lits, Lits+2 ) )
            assert( 0 );
    }
    // add CNF to the SAT solver
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( m_pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            break;
    if ( i < pCnf->nClauses )
        printf( "SAT solver became UNSAT after adding clauses.\n" );
}

Cnf_Dat_t* AbcMcInterface::createCNFRepresentation()
{
    // Reconstruct the unrolled model as an AIG.
    Aig_Man_t* pUnrolledAig = convertUnrolledModelToAig();

    // Translate the new AIG to a CNF object
    Cnf_Dat_t* pCnf = Cnf_Derive(pUnrolledAig, Aig_ManCoNum(pUnrolledAig));

    Cnf_DataLift(pCnf, m_nSatVars);
    m_nSatVars += pCnf->nVars;
    return pCnf;
}

eResult AbcMcInterface::solveSat()
{
    Aig_Obj_t * pObj;
    int i, k, VarNum, Lit, status, RetValue;
    assert( Vec_PtrSize(m_vTargets) > 0 );
    if ( m_pSat->qtail != m_pSat->qhead )
    {
        RetValue = sat_solver_simplify(m_pSat);
        assert( RetValue != 0 );
    }
    Vec_PtrForEachEntry( Aig_Obj_t *, m_vTargets, pObj, i )
    {
        //if ( m_nConfMaxAll && m_pSat->stats.conflicts > m_nConfMaxAll )
        //    return l_Undef;
        VarNum = getSatNum(Aig_Regular(pObj));
        Lit = toLitCond( VarNum, Aig_IsComplement(pObj) );
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
            continue;
        }
        if ( RetValue == l_Undef ) // undecided
            return UNDEF;

        // generate counter-example
        //m_pAig->pSeqModel = ??

        return TRUE;
    }
    return FALSE;
}

Aig_Man_t* AbcMcInterface::convertUnrolledModelToAig()
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManForEachObj( m_pFrm, pObj, i )
        assert( pObj->pData == NULL );

    Aig_Man_t* pNew = Aig_ManStart(0);
    Aig_ManConst1(m_pFrm)->pData = Aig_ManConst1(pNew);
    Vec_IntClear( m_vVisited );
    Vec_IntPush( m_vVisited, Aig_ObjId(Aig_ManConst1(m_pFrm)) );
    Vec_PtrForEachEntry( Aig_Obj_t *, m_vTargets, pObj, i )
    {
        Aig_Obj_t* pObjNew = convertUnrolledModelToAig_rec(pNew, Aig_Regular(pObj) );
        assert( !Aig_IsComplement(pObjNew) );
        Aig_ObjCreateCo( pNew, pObjNew );
    }
    return pNew;
}


Aig_Obj_t * AbcMcInterface::constructFrameFromOutput_rec(Aig_Obj_t * pObj, int i, Vec_Int_t * vVisited)
{
    Aig_Obj_t * pRes;
    pRes = getObjForFrame(pObj, i );
    if ( pRes != NULL )
        return pRes;

    // 1. For each PI, simply create a CI.
    // 2. For each LO, CO or just a node traverse backwards to create the logic.
    if ( Saig_ObjIsPi( m_pAig, pObj ) )
        pRes = Aig_ObjCreateCi(m_pFrm);
    else if ( Saig_ObjIsLo( m_pAig, pObj ) )
        pRes = constructFrameFromOutput_rec(Saig_ObjLoToLi(m_pAig, pObj), i-1, vVisited );
    else if ( Aig_ObjIsCo( pObj ) )
    {
        constructFrameFromOutput_rec(Aig_ObjFanin0(pObj), i, vVisited );
        pRes = getObjChild0(pObj, i );
    }
    else
    {
        constructFrameFromOutput_rec(Aig_ObjFanin0(pObj), i, vVisited );
        if ( getObjChild0(pObj, i) == Aig_ManConst0(m_pFrm) )
            pRes = Aig_ManConst0(m_pFrm);
        else
        {
            constructFrameFromOutput_rec(Aig_ObjFanin1(pObj), i, vVisited );
            pRes = Aig_And( m_pFrm, getObjChild0(pObj, i), getObjChild1(pObj, i) );
        }
    }
    assert( pRes != NULL );
    setMappingForFrame(pObj, i, pRes );
    Vec_IntPush( vVisited, Aig_ObjId(pObj) );
    Vec_IntPush( vVisited, i );
    return pRes;
}

Aig_Obj_t * AbcMcInterface::convertUnrolledModelToAig_rec(Aig_Man_t * pNew, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return (Aig_Obj_t *)pObj->pData;
    Vec_IntPush( m_vVisited, Aig_ObjId(pObj) );
    if ( getSatNum(pObj) || Aig_ObjIsCi(pObj) )
    {
        m_nStitchVars += !Aig_ObjIsCi(pObj);
        return (Aig_Obj_t *)(pObj->pData = Aig_ObjCreateCi(pNew));
    }
    convertUnrolledModelToAig_rec(pNew, Aig_ObjFanin0(pObj) );
    convertUnrolledModelToAig_rec(pNew, Aig_ObjFanin1(pObj) );
    assert( pObj->pData == NULL );
    return (Aig_Obj_t *)(pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) ));
}

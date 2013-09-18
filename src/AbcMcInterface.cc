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
#include "aig/gia/giaAig.h"

using namespace abc;

#define DEBUG 0

//extern int Cmd_CommandExecute(void *pAbc, char *sCommand);

Aig_Man_t* reEncode(Aig_Man_t* p)
{
    // Only support single property for now.
    assert(p->nTruePos == 1);
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
    Aig_Obj_t* pPI = Aig_ObjCreateCi(pNew);
    Aig_ManForEachCi( p, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );
    // set registers
    pNew->nTruePis = p->nTruePis+1;
    pNew->nTruePos = p->nTruePos;
    pNew->nRegs    = p->nRegs;
    pNew->nConstrs = Saig_ManConstrNum(p);
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );

    Aig_Obj_t *pLi, *pLo;
    Saig_ManForEachLiLo( p, pLi, pLo, i )
    {
        //Aig_Obj_t* ppp = Aig_Or(pNew, Aig_Not(pPI), Aig_Not(Aig_ObjCopy(pLo)));
        Aig_Obj_t* pTmp = Aig_And(pNew, Aig_ObjChild0Copy(pLi), Aig_Not(pPI));
        Aig_Regular(pLi->pFanin0)->pData = pTmp;
        pLi->pFanin0 = Aig_Regular(pLi->pFanin0);
    }

    // add the PO
    pObj = Aig_ManCo(p, 0 );
    Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj) );

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

AbcMcInterface::AbcMcInterface(string strFileName) :
      m_pSat(NULL)
    , m_iFramePrev(0)
    , m_nLastFrame(0)
    , m_ClausesByFrame(1)
    , m_VarsByFrame(1)
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
    Aig_Man_t* pTmpCircuit = Abc_NtkToDar(pNtk, 0, 1);

    // Wanna be on the safe side with the ABC framework, so going to stop it
    // and reload. Otherwise, the ABC Network will not be in-sync with the underlying
    // AIG.
    std::cout << "\tRe-Encoding the circuit and dumping to __tmp.aig.\n";
    pTmpCircuit = reEncode(pTmpCircuit);
    char sfx[] = "__tmp.aig";
    Ioa_WriteAiger(pTmpCircuit, sfx,1,0);
    std::cout << "\tDestroying ABC and restarting...\n";
    Abc_Stop();

    Abc_Start();
    m_pAbcFramework = Abc_FrameGetGlobalFrame();

    std::cout << "\tReading the AIG...\n";
    Cmd_CommandExecute(m_pAbcFramework, "read __tmp.aig");

    std::cout << "\tGetting the network from the ABC frame.\n";
    pNtk = Abc_FrameReadNtk(m_pAbcFramework);
    m_pAig = Abc_NtkToDar(pNtk, 0, 1);

    m_pOneTR = duplicateAigWithoutPOs(m_pAig);
    m_pOneTRCnf = Cnf_Derive(m_pOneTR, Aig_ManRegNum(m_pOneTR));
    createInitMan();
    createBadMan();
    m_pInitCnf = Cnf_Derive(m_pInit, 0);
    //Cnf_DataWriteIntoFile(m_pInitCnf, "init1.cnf", 0, NULL, NULL);
    m_pBadCnf = Cnf_Derive(m_pBad, Aig_ManCoNum(m_pBad));
    //Cnf_DataWriteIntoFile(m_pBadCnf, "bad.cnf", 0, NULL, NULL);

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

                int nVar = m_pOneTRCnf->pVarNums[pObj2->Id];

                Lits[0] = toLitCond(m_pInitCnf->pVarNums[pObj->Id], 0 );
                Lits[1] = toLitCond(nVar, 1 );
                addClauseToSat(Lits, Lits+2);

                Lits[0] = toLitCond(m_pInitCnf->pVarNums[pObj->Id], 1 );
                Lits[1] = toLitCond(nVar, 0 );
                addClauseToSat(Lits, Lits+2);
            }
        }
        else
        {
            Saig_ManForEachLo( m_pOneTR, pObj, i )
            {
                Aig_Obj_t *pObj2 = Saig_ManLi(m_pOneTR, i );

                int nVar = m_pOneTRCnf->pVarNums[pObj->Id]; // This is the global var.
                int nVar2 = m_pOneTRCnf->pVarNums[pObj2->Id] - m_pOneTRCnf->nVars - m_pBadCnf->nVars;

                Lits[0] = toLitCond(nVar , 0 );
                Lits[1] = toLitCond(nVar2, 1 );
                addClauseToSat(Lits, Lits+2);

                Lits[0] = toLitCond(nVar , 1 );
                Lits[1] = toLitCond(nVar2, 0 );
                addClauseToSat(Lits, Lits+2);
            }
        }

        if (addCNFToSAT(m_pOneTRCnf) == false)
            assert(false);

        logCnfVars(m_pOneTR, m_pOneTRCnf);

        Cnf_DataLift(m_pOneTRCnf, m_pOneTRCnf->nVars + m_pBadCnf->nVars);
    }
#if DEBUG
    sat_solver_store_write(m_pSat, "init_tr.cnf");
#endif
    Cnf_DataLift(m_pOneTRCnf, -nDelta - (nTo-nFrom)*(m_pOneTRCnf->nVars + m_pBadCnf->nVars));
}

// ************************************************************************
// Collect the global variables for an unrolling of a BMC formula.
// ************************************************************************
void AbcMcInterface::prepareGlobalVars(int nFrame)
{
    int nDelta = m_pInitCnf->nVars + (nFrame-1)*(m_pOneTRCnf->nVars + m_pBadCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, nDelta);

    m_GlobalVars.resize(nFrame);

    Aig_Obj_t *pObj;
    int i, Lits[2];
    if (nFrame == 1)
    {
        Saig_ManForEachLi(m_pOneTR, pObj, i)
        {
            int nVar = m_pOneTRCnf->pVarNums[pObj->Id];
            m_GlobalVars[nFrame-1].push_back(nVar);
        }
    }
    else
    {
        Saig_ManForEachLo( m_pOneTR, pObj, i )
        {
            Aig_Obj_t *pObj2 = Saig_ManLi(m_pOneTR, i );

            int nVar = m_pOneTRCnf->pVarNums[pObj2->Id]; // This is the global var.

            m_GlobalVars[nFrame-1].push_back(nVar);
        }
    }


    Cnf_DataLift(m_pOneTRCnf, -nDelta);
}

bool AbcMcInterface::addCNFToSAT(Cnf_Dat_t *pCnf)
{
    for (int i = 0; i < pCnf->nClauses; i++)
    {
        if ( addClauseToSat(pCnf->pClauses[i], pCnf->pClauses[i+1]) == false)
        {
            return false;
        }
    }
    return true;
}

eResult AbcMcInterface::solveSat()
{
    Aig_Obj_t * pObj;
    int i, k, VarNum, Lit, RetValue;

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
    //sat_solver_bookmark(m_pSat);
    VarNum = m_pBadCnf->pVarNums[pObj->Id] + (m_pInitCnf->nVars) + (m_nLastFrame - 1)*(m_pOneTRCnf->nVars + m_pBadCnf->nVars) + m_pOneTRCnf->nVars;
    Lit = toLitCond( VarNum, Aig_IsComplement(pObj) ) ;
    addClauseToSat(&Lit, &Lit +1);
    markPartition(m_nLastFrame);
    sat_solver_store_mark_roots( m_pSat );
    //RetValue = sat_solver_solve( m_pSat, &Lit, &Lit + 1, (ABC_INT64_T)10000000, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    RetValue = sat_solver_solve( m_pSat, NULL,  NULL, (ABC_INT64_T)10000000, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

    if ( RetValue == l_False ) // unsat
    {
        // add final unit clause
#if 0
        Lit = lit_neg( Lit );
        addClauseToSat(&Lit, &Lit + 1);
        // add learned units
        /*for ( k = 0; k < veci_size(&m_pSat->unit_lits); k++ )
        {
            Lit = veci_begin(&m_pSat->unit_lits)[k];
            status = sat_solver_addclause( m_pSat, &Lit, &Lit + 1, 0 );
            assert( status );
        }
        veci_resize(&m_pSat->unit_lits, 0);*/
        // propagate units
        if (m_pSat->qtail != m_pSat->qhead )
        {
            int RetValue = sat_solver_simplify(m_pSat);
            assert( RetValue != 0 );
            //sat_solver_compress( m_pSat );
        }
#endif

        //sat_solver_rollback(m_pSat);
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
Aig_Man_t* AbcMcInterface::getInterpolationSeq()
{
    void* pSatCnf = sat_solver_store_release( m_pSat );
    sat_solver_delete( m_pSat );
    m_pSat = NULL;
    Vec_Int_t** vSharedVars = ABC_ALLOC(Vec_Int_t*, m_nLastFrame);

    // Prepare the variables shared between two partitions in a BMC formula.
    for (int i=0; i < m_nLastFrame; i++)
    {
        vSharedVars[i] = Vec_IntAlloc(Aig_ManRegNum(m_pAig));
        assert(Aig_ManRegNum(m_pAig) == m_GlobalVars[i].size());
        for (int j=0; j < Aig_ManRegNum(m_pAig); j++)
        {
            Vec_IntPush(vSharedVars[i], m_GlobalVars[i][j]);
        }

        /*Inta_Man_t* pManInter = Inta_ManAlloc();
        Aig_Man_t* pMan = (Aig_Man_t *)Inta_ManInterpolate( pManInter, (Sto_Man_t *)pSatCnf, 0, (void*)vSharedVars[0], 0 );
        Inta_ManFree( pManInter );
        Aig_ManPrintStats(pMan);
        return pMan;*/
    }

    // Create the interpolating manager and extract the interpolation-seq
    Ints_Man_t* pManInter = Ints_ManAlloc(m_nLastFrame);
    Aig_Man_t* pMan = (Aig_Man_t *)Ints_ManInterpolate( pManInter, (Sto_Man_t *)pSatCnf, 0, (void**)vSharedVars, 0 );
    Ints_ManFree( pManInter );

    //Gia_Man_t* pInter = (Gia_Man_t *)Int2_ManReadInterpolant( m_pSat );
    //Gia_ManPrintStats( pInter, 0, 0, 0 );
    Aig_ManPrintStats(pMan);
    Aig_ManDump(pMan);
    Aig_ManCleanData(pMan);
    //pMan->nTruePis = Aig_ManCiNum(pMan);
    //pMan->nTruePos = Aig_ManCoNum(pMan);
    //pMan->nRegs = 0;

    // Release memory
    Sto_ManFree( (Sto_Man_t *)pSatCnf );
    for (int i=0; i < m_nLastFrame; i++)
        Vec_IntErase(vSharedVars[i]);
    ABC_FREE(vSharedVars);
    return pMan;
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

Aig_Man_t* AbcMcInterface::duplicateAigWithNewPO(Aig_Man_t* pMan, Aig_Obj_t *pNewPO)
{
    Aig_Man_t* p = m_pAig;
    // Only one property output.
    assert(Saig_ManPoNum(p) - Saig_ManConstrNum(p) == 1);

    assert( Aig_ManRegNum(p) > 0 );
    // create the new manager
    Aig_Man_t *pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);

    int i;
    Aig_Obj_t * pObj;
    Aig_ManForEachCi( p, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );

    // set registers
    pNew->nTruePis = p->nTruePis;
    pNew->nTruePos = Saig_ManConstrNum(p) + 1;
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

    assert(Aig_ManCiNum(pMan) == Saig_ManRegNum(pNew));

    // Now set the "leaves" of the interpolant manager.
    Saig_ManForEachLo(m_pAig, pObj, i)
    {
        assert(Aig_ManCiNum(pMan) > i);
        Aig_Obj_t* pIntObj = Aig_ManCi(pMan, i);
        pIntObj->pData = pObj->pData;
    }

    Aig_ManForEachCi(pMan, pObj, i)
        assert(pObj->pData != NULL);

    Aig_ManForEachNode(pMan, pObj, i)
    {
        //cout << "Creating node: " << i << endl;
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        assert(pObj->pData != NULL);
    }

    // Create the new output
    pObj = createCombSlice_rec(pMan, pNew, Aig_ObjChild0(pNewPO)); // Is this needed in this case?
    //assert(pObj == Aig_ObjChild0Copy(pNewPO));
    Aig_ObjCreateCo(pNew, Aig_Not(Aig_ObjChild0Copy(pNewPO)));

    Saig_ManForEachLi( p, pObj, i )
        Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pNew );
    Aig_ManCleanData(pMan);
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

Aig_Man_t* AbcMcInterface::createArbitraryCombMan(Aig_Man_t* pMan, int nOut)
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

bool AbcMcInterface::setInit()
{
    logCnfVars(m_pInit, m_pInitCnf);
    bool bRes = addCNFToSAT(m_pInitCnf);
    //sat_solver_store_write(m_pSat, "init.cnf");
    return bRes;
}

bool AbcMcInterface::setBad(int nFrame, bool bHasPIs)
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
        Aig_Obj_t* pObj2 = Aig_ManCi(m_pBad, (bHasPIs) ? m_pOneTR->nTruePis+i : i );

        int nVar  = m_pOneTRCnf->pVarNums[pObj->Id];
        int nVar2 = m_pBadCnf->pVarNums[pObj2->Id]; // This is a global var

        //m_GlobalVars[m_nLastFrame].push_back(nVar2);

        Lits[0] = toLitCond(nVar , 0 );
        Lits[1] = toLitCond(nVar2, 1 );
        addClauseToSat(Lits, Lits+2);

        Lits[0] = toLitCond(nVar , 1 );
        Lits[1] = toLitCond(nVar2, 0 );
        addClauseToSat(Lits, Lits+2);
    }

    bool bRes = addCNFToSAT(m_pBadCnf);
    logCnfVars(m_pBad, m_pBadCnf);

    // Revert CNF to its original state
    Cnf_DataLift(m_pBadCnf, -nDelta - m_pOneTRCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, -nDelta);

    assert(bRes);

    return bRes;
}

Aig_Obj_t* AbcMcInterface::createCombSlice_rec(Aig_Man_t* pOrig, Aig_Man_t* pMan, Aig_Obj_t * pObj)
{
    Aig_Obj_t * pRes = (Aig_Obj_t*)(pObj->pData);
    if ( pRes != NULL )
        return pRes;

    // 1. For each PI and LO, simply create a CI.
    // 2. For each LO, CO or just a node, traverse backwards to create the logic.
    if ( Aig_ObjIsCi(pObj))
        pRes = Aig_ObjCreateCi(pMan);
    else if ( Aig_ObjIsCo( pObj ) )
    {
        // Can this happen for comb slice?!
        assert(false);
    }
    else
    {
        createCombSlice_rec(pOrig, pMan, Aig_ObjFanin0(pObj));
        createCombSlice_rec(pOrig, pMan, Aig_ObjFanin1(pObj));

        pRes = Aig_And( pMan, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    }
    assert( pRes != NULL );
    pObj->pData = pRes;
    return pRes;
}


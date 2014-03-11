/*
 * AbcMcInterface.cc
 *
 *  Created on: Jul 25, 2013
 *      Author: yakir
 */

#include <stdio.h>
#include <assert.h>
#include <iostream>

#include "avy/Util/AvyAssert.h"
#include "AigUtils.h"

#include "AbcMcInterface.h"
#include "base/main/main.h"
#include "aig/ioa/ioa.h"

using namespace avy::abc;
using namespace avy;

#define DEBUG 0


AbcMcInterface::AbcMcInterface(string strFileName) :
      m_pSat(NULL)
    , m_iFramePrev(0)
    , m_nLastFrame(0)
    , m_ClausesByFrame(1)
    , m_VarsByFrame(1)
    , m_pBadStore (NULL)
    , m_pInitStore(NULL)
    , m_bTrivial(false)
    , m_bAddGlueRemovalLiteral(false)
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
    Gia_Man_t* pGia = Gia_ManFromAigSimple(pTmpCircuit);
    Aig_ManStop(pTmpCircuit);
    Gia_Man_t* pRe = Gia_ManDupSelf(pGia);
    Gia_ManStop(pGia);
    pTmpCircuit = Gia_ManToAigSimple(pRe);
    Gia_ManStop(pRe);
    //Aig_Man_t *pTmpCircuit2 = Aig_AddResetPi (pTmpCircuit);
    // -- XXX Should the circuit be stoped, or is it cleared by Abc?
    //Aig_ManStop (pTmpCircuit);
    //pTmpCircuit = pTmpCircuit2;

    char sfx[] = "__tmp.aig";
    Ioa_WriteAiger(pTmpCircuit, sfx,1,0);
    std::cout << "\tDestroying ABC and restarting...\n";
    // XXX Should pTmpCircuit be stopped?
    Abc_Stop();

    Abc_Start();
    m_pAbcFramework = Abc_FrameGetGlobalFrame();

    std::cout << "\tReading the AIG...\n";
    Cmd_CommandExecute(m_pAbcFramework, "read __tmp.aig");

    std::cout << "\tGetting the network from the ABC frame.\n";
    pNtk = Abc_FrameReadNtk(m_pAbcFramework);
    m_pAig = Abc_NtkToDar(pNtk, 0, 1);

    m_pOneTR = Aig_ManDupNoPo (m_pAig);
    m_pOneTRCnf = Cnf_Derive(m_pOneTR, Aig_ManRegNum(m_pOneTR));
    createInitMan();
    createBadMan();
    m_pInitCnf = Cnf_Derive(m_pInit, 0);
    //Cnf_DataWriteIntoFile(m_pInitCnf, "init1.cnf", 0, NULL, NULL);
    m_pBadCnf = Cnf_Derive(m_pBad, Aig_ManCoNum(m_pBad));
    //Cnf_DataWriteIntoFile(m_pBadCnf, "bad.cnf", 0, NULL, NULL);

    std::cout << m_pInitCnf->nVars << " " << m_pOneTRCnf->nVars 
              << " " << m_pBadCnf->nVars << "\n";
    std::cout << "Done setting up ABC.\n";
}

void AbcMcInterface::addTransitionsFromTo(int nFrom, int nTo)
{
	assert(nFrom >= 0 && nFrom == m_nLastFrame && nFrom < nTo);

    m_iFramePrev = m_nLastFrame;
    int nDelta = m_pInitCnf->nVars + (nFrom)*(m_pOneTRCnf->nVars);// + m_pBadCnf->nVars);
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
                
                // -- connect intitial state with Lo of Tr
                // -- add forall i . Init.Ci.i = TR1.Lo.i
                
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

                int nVar = m_pOneTRCnf->pVarNums[pObj->Id]; 
                // This is the global var.
                int nVar2 = m_pOneTRCnf->pVarNums[pObj2->Id] - m_pOneTRCnf->nVars;// - m_pBadCnf->nVars;

                // -- add forall i . Tr_{from}.Li.i = TR_{from+1}.Lo.i
                // -- latch inputs are global (i.e., output of TR_i is global)
                // -- this is more uniform than taken latch outpus as global

                Lits[0] = toLitCond(nVar , 0 );
                Lits[1] = toLitCond(nVar2, 1 );
                addClauseToSat(Lits, Lits+2);

                Lits[0] = toLitCond(nVar , 1 );
                Lits[1] = toLitCond(nVar2, 0 );
                addClauseToSat(Lits, Lits+2);
            }
        }

        assert(addCNFToSAT(m_pOneTRCnf) != false);

        Cnf_DataLift(m_pOneTRCnf, m_pOneTRCnf->nVars);
    }
#if DEBUG
    sat_solver_store_write(m_pSat, "init_tr.cnf");
#endif
    Cnf_DataLift(m_pOneTRCnf, 
                 -nDelta - (nTo-nFrom)*(m_pOneTRCnf->nVars));
}

// ************************************************************************
// Collect the global variables for an unrolling of a BMC formula.
// ************************************************************************
void AbcMcInterface::prepareGlobalVars(int nFrame)
{
    int nDelta = m_pInitCnf->nVars + (nFrame-1)*(m_pOneTRCnf->nVars);

    m_GlobalVars.resize(nFrame);

    Aig_Obj_t *pObj;
    int i, Lits[2];
    Saig_ManForEachLi(m_pOneTR, pObj, i)
    {
        int nVar = m_pOneTRCnf->pVarNums[pObj->Id] + nDelta;
        m_GlobalVars[nFrame-1].push_back(nVar);
    }
}

bool AbcMcInterface::addCNFToSAT(Cnf_Dat_t *pCnf)
{
    for (int i = 0; i < pCnf->nClauses; i++)
    {
        if ( addClauseToSat(pCnf->pClauses[i], pCnf->pClauses[i+1]) == false)
          return false;
    }
    return true;
}

eResult AbcMcInterface::solveSat()
{
    Aig_Obj_t * pObj;
    int i, k, VarNum, Lit, RetValue;

    pObj = Aig_ManCo(m_pBad, 0);
# if DEBUG
    std::ostringstream os;
    os << "yakir_" << m_nLastFrame << ".cnf";
    const char* name = os.str().c_str();
    sat_solver_store_write(m_pSat, (char*)name);
#endif
    //sat_solver_bookmark(m_pSat);
    // XXX Seems like the formula below can be simplified.
    VarNum = m_pBadCnf->pVarNums[pObj->Id] + 
      (m_pInitCnf->nVars) + (m_nLastFrame - 1)*(m_pOneTRCnf->nVars) +
      m_pOneTRCnf->nVars;

    Lit = toLitCond( VarNum, Aig_IsComplement(pObj) ) ;
    if (addClauseToSat(&Lit, &Lit +1) == false)
    {
        m_bTrivial = true;
        return FALSE;
    }
    markPartition(m_nLastFrame);
    sat_solver_store_mark_roots( m_pSat );
    RetValue = sat_solver_solve( m_pSat, NULL,  NULL, 
                                 (ABC_INT64_T)10000000, (ABC_INT64_T)0, 
                                 (ABC_INT64_T)0, (ABC_INT64_T)0 );

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
    if (m_bTrivial == true)
    {
        assert(m_pAig->nRegs > 0);
        Aig_Man_t* pMan = Aig_ManStart(10000);
        Aig_IthVar(pMan, m_pAig->nRegs-1);
        for (int i=0; i < m_nLastFrame; i++)
            Aig_ObjCreateCo(pMan, Aig_ManConst1(pMan));
        return pMan;
    }
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
    Aig_Man_t* pMan = (Aig_Man_t *)Ints_ManInterpolate( pManInter,
                                                        (Sto_Man_t *)pSatCnf, 
                                                        0, (void**)vSharedVars,
                                                        0 );
    Ints_ManFree( pManInter );

    Aig_Man_t *tmp = Aig_ManSimplifyComb (pMan);
    Aig_ManStop (pMan);
    pMan = tmp; tmp = NULL;

    Aig_ManPrintStats(pMan);

    // Release memory
    Sto_ManFree( (Sto_Man_t *)pSatCnf );
    for (int i=0; i < m_nLastFrame; i++) Vec_IntErase (vSharedVars[i]);
    ABC_FREE(vSharedVars);
    return pMan;
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
    bool bRes = addCNFToSAT(m_pInitCnf);
    //sat_solver_store_write(m_pSat, "init.cnf");
    return bRes;
}

bool AbcMcInterface::setBad(int nFrame, bool bHasPIs)
{
    assert(nFrame > 0);
    int nDelta = m_pInitCnf->nVars +
                 (nFrame-1)*(m_pOneTRCnf->nVars);// + m_pBadCnf->nVars);

    // Prepare CNF.
    Cnf_DataLift(m_pBadCnf, nDelta + m_pOneTRCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, nDelta);



    Aig_Obj_t* pObj;
    int i, Lits[2];
    Saig_ManForEachLi(m_pOneTR, pObj, i)
    {
        assert ( i <= Aig_ManRegNum(m_pOneTR));
        Aig_Obj_t* pObj2 = Aig_ManCi(m_pBad, (bHasPIs) ? m_pOneTR->nTruePis+i : i );

        int nVar  = m_pOneTRCnf->pVarNums[pObj->Id]; // This is a global var
        int nVar2 = m_pBadCnf->pVarNums[pObj2->Id]; 


        Lits[0] = toLitCond(nVar , 0 );
        Lits[1] = toLitCond(nVar2, 1 );
        addClauseToSat(Lits, Lits+2);

        Lits[0] = toLitCond(nVar , 1 );
        Lits[1] = toLitCond(nVar2, 0 );
        addClauseToSat(Lits, Lits+2);
    }

    bool bRes = addCNFToSAT(m_pBadCnf);

    // Revert CNF to its original state
    Cnf_DataLift(m_pBadCnf, -nDelta - m_pOneTRCnf->nVars);
    Cnf_DataLift(m_pOneTRCnf, -nDelta);

    assert(bRes);

    return bRes;
}


void AbcMcInterface::addClausesToFrame(Vec_Ptr_t* pCubes, int nFrame)
{
    int nDelta = m_pInitCnf->nVars + (nFrame)*(m_pOneTRCnf->nVars);// + (nFrame-1)*(m_pBadCnf->nVars);
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

        bool bRes = addClauseToSat(pClause, pClause+nCounter);
        assert(bRes);
        ABC_FREE(pClause);
    }
}


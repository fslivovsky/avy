#ifndef ABC_MC_INTERFACE_H
#define ABC_MC_INTERFACE_H

#include "../abc/src/aig/aig/aig.h"
#include "../abc/src/aig/saig/saig.h"
#include "../abc/src/sat/cnf/cnf.h"
#include "../abc/src/base/main/main.h"
#include "../abc/src/base/abc/abc.h"
#include "../abc/src/misc/vec/vec.h"
#include "../abc/src/sat/bsat/satStore.h"

#include <string>

// An interface to the ABC framework.
// Should give utilities such as:
// 1. Unrolling of a transition relation
// 2. Setting and Getting the initial states
// 3. Generation of CNF formula
//
// Can also be implemented for other frameworks: add an Interface class
// with general utility functions (class AbcMcInterface : public McInterface).

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

enum eResult {
    FALSE = -1,
    UNDEF = 0,
    TRUE = 1
};

class AbcMcInterface
{
public:

    AbcMcInterface(std::string strFileName);

	~AbcMcInterface()
	{
		Abc_Stop();
	}

	// Updates pUnrolledTR to an AIG representing an unrolling of the TR from
	// phase nFrom to phase nTo. It should be possible to create the
	// unrolling in an incremental fashion.
	// NOTE: The property is not asserted in the resulting AIG.
	void addTransitionsFromTo(int nFrom, int nTo);

	void updateSATSolverWithCNF(Cnf_Dat_t *pCnf);

	Cnf_Dat_t* createCNFRepresentation();
	void destroyCnfRepresentation(Cnf_Dat_t* pCnf)
	{
	    Aig_Man_t* pAig = pCnf->pMan;
	    Cnf_DataFree( pCnf );
        Aig_ManStop( pAig );
	}

	eResult solveSat();

private:
	Aig_Obj_t * constructFrameFromOutput_rec(Aig_Obj_t *pObj, int i, Vec_Int_t *vVisited);

	Aig_Man_t* convertUnrolledModelToAig();
	Aig_Obj_t* convertUnrolledModelToAig_rec(Aig_Man_t *pNew, Aig_Obj_t *pObj);

	// ************************************************************************
    // Mapping functions (get and set) from Rolled Model to Unrolled model
	// based on time frames.
    // ************************************************************************
	inline Aig_Obj_t * getObjForFrame(Aig_Obj_t* pObj, int i)
	{
	    // Get mapping for i-th frame
	    Vec_Int_t * vFrame = (Vec_Int_t *)Vec_PtrEntry(m_vAig2Frm, i );

	    // Get the number for the representative at the i-th frame
	    int iObjLit = Vec_IntEntry( vFrame, Aig_ObjId(pObj) );
	    if ( iObjLit == -1 )
	        return NULL;

	    // Get the actual object
	    Aig_Obj_t* pRes = Aig_ManObj(m_pFrm, Abc_Lit2Var(iObjLit) );

	    if ( pRes == NULL )
	        Vec_IntWriteEntry( vFrame, Aig_ObjId(pObj), -1 );
	    else
	        pRes = Aig_NotCond( pRes, Abc_LitIsCompl(iObjLit) );

	    return pRes;
	}

	inline void setMappingForFrame(Aig_Obj_t* pObj, int i, Aig_Obj_t* pNode)
    {
	    // Check that there are enough entries in the Vector.
        if ( i == Vec_PtrSize(m_vAig2Frm) )
            Vec_PtrPush( m_vAig2Frm, Vec_IntStartFull(m_nObjs) );
        assert( i < Vec_PtrSize(m_vAig2Frm) );

        // Get the mapping for the i-th frame.
        Vec_Int_t* vFrame = (Vec_Int_t *)Vec_PtrEntry( m_vAig2Frm, i );

        int iObjLit = -1;
        if ( pNode != NULL ) {
            iObjLit = Abc_Var2Lit( Aig_ObjId(Aig_Regular(pNode)), Aig_IsComplement(pNode) );
        }

        // Set the mapping.
        Vec_IntWriteEntry( vFrame, Aig_ObjId(pObj), iObjLit );
    }

	// ************************************************************************
	// During translation, an object representative is stored in the Data field
	// Utilities function (getObjChild0 and getObjChild1) to extract this info
	// during "traversal" and creation of an unrolled model.
	// ************************************************************************
	inline Aig_Obj_t * getObjChild0(Aig_Obj_t * pObj, int i )
	{
	    assert( !Aig_IsComplement(pObj) );
	    return Aig_NotCond(getObjForFrame(Aig_ObjFanin0(pObj), i), Aig_ObjFaninC0(pObj));
	}

	inline Aig_Obj_t * getObjChild1(Aig_Obj_t * pObj, int i )
	{
	    assert( !Aig_IsComplement(pObj) );
	    return Aig_NotCond(getObjForFrame(Aig_ObjFanin1(pObj), i), Aig_ObjFaninC1(pObj));
	}

	// ************************************************************************
	// Mapping functions. From an Unrolled Model variable (or node) to the
	// corresponding SAT variable.
	// ************************************************************************
	inline int getSatNum(Aig_Obj_t * pObj )
	{
	    return Vec_IntGetEntry(m_vObj2Var, pObj->Id );
	}

	inline void setSatMapping(Aig_Obj_t* pObj, int Num )
	{
	    Vec_IntSetEntry(m_vObj2Var, pObj->Id, Num);
	}

private:
	Abc_Frame_t* 	      m_pAbcFramework;

	// AIG managers
    Aig_Man_t *           m_pAig;           // The rolled model
    Aig_Man_t *           m_pFrm;           // The unrolled model
    Vec_Int_t *           m_vVisited;       // nodes visited in unrolled model

    // node mapping
    int                   m_nObjs;          // the largest number of an AIG object
    Vec_Ptr_t *           m_vAig2Frm;       // mapping of AIG nodees into Frames nodes

    // SAT solver
    sat_solver *          m_pSat;           // SAT solver
    int                   m_nSatVars;       // the number of used SAT variables
    Vec_Int_t *           m_vObj2Var;       // mapping of frames objects in CNF variables
    int                   m_nStitchVars;

    // subproblems
    Vec_Ptr_t *           m_vTargets;       // targets to be solved in this interval
    int                   m_iFramePrev;     // previous frame
    int                   m_nLastFrame;     // last frame
};

#endif // ABC_MC_INTERFACE_H

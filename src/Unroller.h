#ifndef _UNROLLER_H_
#define _UNROLLER_H_

#include <cassert>

#include <vector>
#include "misc/vec/vec.h"
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"

#include "boost/foreach.hpp"
#include "boost/dynamic_bitset.hpp"
#include "boost/logic/tribool.hpp"

#include "avy/AvyAbc.h"
#include "avy/Util/Global.h"

namespace avy
{
  template <typename SatSolver>
  class Unroller
  {
    /// smart pointer for Cnf_Dat_t.
	typedef boost::shared_ptr<Cnf_Dat_t> CnfPtr;

    SatSolver *m_pSolver;
    unsigned m_nVars;
    unsigned m_nFrames;

    /// Primary Inputs, by frame
    std::vector<avy::abc::Vec_Int_t*> m_vPrimaryInputs;
    /// Inputs, by frame
    std::vector<avy::abc::Vec_Int_t*> m_vInputs;
    /// Outputs, by frame
    std::vector<avy::abc::Vec_Int_t*> m_vOutputs;

    /// All assumptions
    std::vector<int> m_Assumps;

    std::vector<std::vector<int> > m_Glued;

    
    /**
     * Start of frame assumptions in m_Assumps
     * m_Assumps[i] is the start of assumptions of frame i in m_Assumps
     */
    std::vector<unsigned> m_FrameAssump;

    boost::dynamic_bitset<> *m_pEnabledAssumps;

    bool m_fWithAssump;
    /// Literal for Bad output
    lit m_BadLit;
  
  
  public:
    Unroller(SatSolver &s, bool fWithAssump = false) : 
      m_pSolver (&s), m_nVars(0), m_nFrames(0),
      m_pEnabledAssumps(0), m_fWithAssump (fWithAssump), 
      m_BadLit (-1)
    { newFrame (); }

    ~Unroller () { reset (NULL); }


    void setBadLit (lit bad) { m_BadLit = bad; }
    lit getBadLit () 
    {
      AVY_ASSERT (m_BadLit >= 0);
      return m_BadLit;
    }
    
    bool pushBadUnit ()
    {
      lit b = getBadLit ();
      return m_pSolver->addClause (&b, &b+1);
    }
    
    

    void setEnabledAssumps (boost::dynamic_bitset<> &v)
    { m_pEnabledAssumps = &v; }

    /** Reset everything */
    void reset (SatSolver *solver)
    {
      BOOST_FOREACH (Vec_Int_t *vVec, m_vPrimaryInputs)
        Vec_IntFree (vVec);
      m_vPrimaryInputs.clear ();
      BOOST_FOREACH (Vec_Int_t *vVec, m_vInputs)
        Vec_IntFree (vVec);
      m_vInputs.clear ();
      
      BOOST_FOREACH (Vec_Int_t *vVec, m_vOutputs)
        Vec_IntFree (vVec);
      m_vOutputs.clear ();

      m_Assumps.clear ();
      m_FrameAssump.clear ();
      
      m_Glued.clear();

      m_nVars = 0;
      m_nFrames = 0;
      m_pEnabledAssumps = NULL;
      
      if (solver)
        {
          m_pSolver = solver;
          newFrame ();
        }
    }
    
    void resetLastFrame ()
    {

      Vec_IntClear (m_vInputs.back());
      Vec_IntClear (m_vPrimaryInputs.back());
      m_Glued.back().clear();
      //m_vInputs.pop_back();

      //Vec_IntFree (m_vOutputs.back());
      //m_vOutputs.pop_back ();

      //m_Assumps.pop_back ();
      //m_FrameAssump.pop_back ();

      //m_nFrames--;
    }

  
    /** allocate a variable */
    unsigned freshVar () 
    { 
      unsigned v = m_nVars++; 
      m_pSolver->reserve (m_nVars);
      return v;
    }
  
    /** allocate a block of variables */
    unsigned freshBlock (unsigned b) 
    {
      unsigned v = m_nVars;
      m_nVars += b;
      m_pSolver->reserve (m_nVars);
      return v;
    }


    /// register literal as an assumption
    void addAssump (lit a) { m_Assumps.push_back (a); }
  
    /// return all assumptions
    std::vector<int> &getAssumps () { return m_Assumps; }

    /// return assumptions for a given frame
    std::pair<int*,int*> getFrameAssumps (unsigned nFrame)
    {
      AVY_ASSERT (nFrame < m_FrameAssump.size ());
      int *bgn = &m_Assumps[0] + m_FrameAssump.at (nFrame);
      int *end = &m_Assumps[0];
      if (nFrame + 1 == m_FrameAssump.size ())
        end += m_Assumps.size ();
      else
        end += m_FrameAssump.at (nFrame + 1);
      return std::make_pair (bgn, end);
    }
  
  
    unsigned frame () { return m_nFrames - 1; }
    
    void newFrame ()
    {
      m_nFrames++;
      m_vPrimaryInputs.push_back (Vec_IntAlloc (16));
      m_vInputs.push_back (Vec_IntAlloc (16));
      m_vOutputs.push_back (Vec_IntAlloc (16));

      m_FrameAssump.push_back (m_Assumps.size ());

      m_Glued.push_back(std::vector<int>());
    }
    
    unsigned frames () { return m_nFrames; }
    
    
    void addPrimaryInput (int in)
    { avy::abc::Vec_IntPush (m_vPrimaryInputs.at (frame ()), in); }

    int getPrimaryInput (unsigned nFrame, int nNum)
    { return avy::abc::Vec_IntEntry (m_vPrimaryInputs.at (nFrame), nNum); }

    avy::abc::Vec_Int_t *getPrimaryInputs (unsigned nFrame) { return m_vPrimaryInputs.at (nFrame); }

    void addInput (int in)
    { avy::abc::Vec_IntPush (m_vInputs.at (frame ()), in); }

    int getInput (unsigned nFrame, int nNum)
    { return avy::abc::Vec_IntEntry (m_vInputs.at (nFrame), nNum); }
  
    avy::abc::Vec_Int_t *getInputs (unsigned nFrame) { return m_vInputs.at (nFrame); }

    void addOutput (int out)
    { avy::abc::Vec_IntPush (m_vOutputs.at (frame ()), out); }

    int getOutput (unsigned nFrame, int nNum)
    { return avy::abc::Vec_IntEntry (m_vOutputs.at (nFrame), nNum); }

    avy::abc::Vec_Int_t *getOutputs (unsigned nFrame) { return m_vOutputs.at (nFrame); }
    std::vector<avy::abc::Vec_Int_t*> &getAllOutputs () { return m_vOutputs; }
    
    void setFrozenOutputs(unsigned nFrame, bool v)
    {
        avy::abc::Vec_Int_t* outputs = m_vOutputs[nFrame];
        int out;
        int i;
        Vec_IntForEachEntry( outputs, out, i )
        {
        	if ( out == -1) continue;
            lit l = toLit(out);
            m_pSolver->setFrozen(lit_var(l), v);
        }

    }

    /** Add clause to solver */
    boost::tribool addClause (avy::abc::lit* beg, avy::abc::lit* end)
    { return m_pSolver->addClause (beg, end); }
  
    boost::tribool addCnf (Cnf_Dat_t* pCnf)
    {
      boost::tribool res = true;
      for (int i = 0; i < pCnf->nClauses; ++i)
        res = res && addClause (pCnf->pClauses [i], pCnf->pClauses [i+1]);
      return res;
    }
    

    boost::tribool eval (lit a)
    {
      boost::tribool res(boost::indeterminate);
      
      if (!m_pEnabledAssumps) return res;
      if (a >= ((lit) m_pEnabledAssumps->size ())) return false;
      return m_pEnabledAssumps->test (a);
    }
    

    void glueOutIn (int nFrame = -1)
    {
      unsigned f = frame();
      if (nFrame != -1) f = nFrame;
      if (gParams.abstraction)
        glueOutIn2 ();
      else
        glueOutIn1 (f);
    }
    
    /** Add glue clauses between current Inputs and previous frame outputs */
    void glueOutIn1 (unsigned nFrame)
    {
      AVY_ASSERT (m_nFrames > 1);
      AVY_ASSERT (Vec_IntSize (m_vOutputs.at (nFrame - 1)) ==
                  Vec_IntSize (m_vInputs.at (nFrame)));

      lit Lit[3];
      unsigned litSz = 2;
      
      int out, i;
    
      Vec_Int_t *ins = m_vInputs.at (nFrame);
      
      std::vector<int>& glued = m_Glued[nFrame];
      if (m_fWithAssump)
        {
    	  int a;
    	  if (glued.size() == 0)
    		  a = freshVar ();
    	  else
    	  {
    		  for (int i=0; i < glued.size(); i++)
    			  if (glued[i] != -1)
    				  a = glued[i];
    	  }
    	  lit aLit = toLit (a);
          
          boost::tribool aVal = eval (aLit);
          if (boost::indeterminate(aVal))
            {
              addAssump (aLit);
              Lit[2] = lit_neg (aLit);
              litSz = 3;
            }
          else if (!aVal) return; // disabled assumption
          // ow, assumption enabled proceed as usual
        }
      
      if (glued.size() == 0) glued.resize(Vec_IntSize(ins), -1);

      Vec_IntForEachEntry (m_vOutputs.at (nFrame - 1), out, i)
        {
    	  if (out == -1 || glued[i] != -1) continue;
    	  if (m_fWithAssump)
    		  glued[i] = lit_var(Lit[2]);
    	  else
    		  glued[i] = 1;
          Lit[0] = toLit (out);
          Lit[1] = toLitCond (Vec_IntEntry (ins, i), 1);
          addClause (Lit, Lit+litSz);
          Lit[0] = lit_neg (Lit[0]);
          Lit[1] = lit_neg (Lit[1]);
          addClause (Lit, Lit+litSz);
        }
    }
    

    void glueOutIn2 ()
    {
      AVY_ASSERT (m_nFrames > 1);
      AVY_ASSERT (Vec_IntSize (m_vOutputs.at (frame () - 1)) == 
                  Vec_IntSize (m_vInputs.at (frame ())));

      lit Lit[3];
      unsigned litSz = 2;
      
      int out, i;
    
      Vec_Int_t *ins = m_vInputs.at (frame ());

      Vec_IntForEachEntry (m_vOutputs.at (frame () - 1), out, i)
        {      
          if (m_fWithAssump)
            {
              int a = freshVar ();
              lit aLit = toLit (a);
          
              boost::tribool aVal = eval (aLit);
              if (!aVal) continue;
              else if (aVal) ; // nothing
              else
                {
                  addAssump (aLit);
                  Lit[2] = lit_neg (aLit);
                  litSz = 3;
                }
            }
      
          Lit[0] = toLit (out);
          Lit[1] = toLitCond (Vec_IntEntry (ins, i), 1);
          addClause (Lit, Lit+litSz);
          Lit[0] = lit_neg (Lit[0]);
          Lit[1] = lit_neg (Lit[1]);
          addClause (Lit, Lit+litSz);
        }
    }
    

    /** Add glue clauses between current Inputs and previous frame outputs */
    void OriginalglueOutIn ()
    {
      AVY_ASSERT (m_nFrames > 1);
      AVY_ASSERT (Vec_IntSize (m_vOutputs.at (frame () - 1)) == 
                  Vec_IntSize (m_vInputs.at (frame ())));
    
      lit Lit[2];
      int out, i;
    
      Vec_Int_t *ins = m_vInputs.at (frame ());
    
      Vec_IntForEachEntry (m_vOutputs.at (frame () - 1), out, i)
        {
          Lit[0] = toLit (out);
          Lit[1] = toLitCond (Vec_IntEntry (ins, i), 1);
          addClause (Lit, Lit+2);
          Lit[0] = lit_neg (Lit[0]);
          Lit[1] = lit_neg (Lit[1]);
          addClause (Lit, Lit+2);
        }
    }

	void addCoiCnf(Aig_Man_t* pAig, const std::vector<int>& roots, CnfPtr pCnf, std::vector<int>& aig2sat)
	{
	  unsigned nSize = roots.size();
	  for (unsigned i=0; i < nSize; i++)
	  {
		  AVY_ASSERT(roots[i] < Aig_ManCoNum(pAig));
		  Aig_Obj_t* pObj = Aig_ManCo(pAig, roots[i]);
		  if ( Aig_ObjFanin0(pObj) == Aig_ManConst0(pAig) )
			  continue;
		  addCoiCnf_rec(pAig, pObj, pCnf, aig2sat);
	  }
	}

	void addCoiCnf_rec(Aig_Man_t* pAig, Aig_Obj_t* pObj, CnfPtr pCnf, std::vector<int>& aig2sat)
	{
	  int iObj = Aig_ObjId( pObj );
	  if ( Aig_ObjIsAnd(pObj) && (&*pCnf)->pObj2Count[iObj] == -1 )
	  {
		  addCoiCnf_rec( pAig, Aig_ObjFanin0(pObj), pCnf, aig2sat );
		  addCoiCnf_rec( pAig, Aig_ObjFanin1(pObj), pCnf, aig2sat );
		  return;
	  }

	  if (aig2sat[(&*pCnf)->pVarNums[iObj]] >= 0) return;

	  aig2sat[(&*pCnf)->pVarNums[iObj]] = freshVar();

	  //assert (Aig_ObjIsConst1(Aig_Regular(pObj)) == false);

	  if ( Aig_ObjIsAnd(pObj) || Aig_ObjIsCo(pObj) )
	  {
		  assert (Aig_ObjIsConst1(Aig_Regular(pObj)) == false);
		  int i, nClas, iCla;
		  addCoiCnf_rec( pAig, Aig_ObjFanin0(pObj), pCnf, aig2sat );
		  if ( Aig_ObjIsAnd(pObj) )
			  addCoiCnf_rec( pAig, Aig_ObjFanin1(pObj), pCnf, aig2sat );
		  // add clauses
		  nClas = (&*pCnf)->pObj2Count[iObj];
		  iCla  = (&*pCnf)->pObj2Clause[iObj];
		  for ( i = 0; i < nClas; i++ )
		  {
			  int nLits, pLits[8];
			  int * pClauseThis = (&*pCnf)->pClauses[iCla+i];
			  int * pClauseNext = (&*pCnf)->pClauses[iCla+i+1];
			  for ( nLits = 0; pClauseThis + nLits < pClauseNext; nLits++ )
			  {
				  if ( pClauseThis[nLits] < 2 )
					  printf( "\n\n\nError in CNF generation:  Constant literal!\n\n\n" );
				  assert( pClauseThis[nLits] > 1 && pClauseThis[nLits] < 2*(Aig_ManObjNum(pAig)+1) );
				  int var = Abc_Lit2Var(pClauseThis[nLits]);
				  pLits[nLits] = Abc_Var2Lit( aig2sat[var], Abc_LitIsCompl(pClauseThis[nLits]) );
			  }
			  assert( nLits < 8 );
			  if ( !this->addClause(pLits, pLits + nLits ) )
				  break;
		  }
		  if ( i < nClas )
			  printf( "SAT solver became UNSAT after adding clauses.\n" );
	  }
	  else if (Aig_ObjIsConst1(Aig_Regular(pObj)))
	  {
		  lit l = toLit(aig2sat[(&*pCnf)->pVarNums[iObj]]);
		  this->addClause(&l, &l + 1);
	  }
	  else assert( Aig_ObjIsCi(pObj) );
	}
  };
}


#endif /* _UNROLLER_H_ */

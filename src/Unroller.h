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
    }
    
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
    

    void glueOutIn ()
    {
      if (gParams.abstraction)
        glueOutIn2 ();
      else
        glueOutIn1 ();
    }
    
    /** Add glue clauses between current Inputs and previous frame outputs */
    void glueOutIn1 ()
    {
      AVY_ASSERT (m_nFrames > 1);
      AVY_ASSERT (Vec_IntSize (m_vOutputs.at (frame () - 1)) == 
                  Vec_IntSize (m_vInputs.at (frame ())));

      lit Lit[3];
      unsigned litSz = 2;
      
      int out, i;
    
      Vec_Int_t *ins = m_vInputs.at (frame ());
      
      if (m_fWithAssump)
        {
          int a = freshVar ();
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
      
      Vec_IntForEachEntry (m_vOutputs.at (frame () - 1), out, i)
        {
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
  };
}


#endif /* _UNROLLER_H_ */

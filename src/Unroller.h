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

namespace avy
{
  template <typename SatSolver>
  class Unroller
  {
    SatSolver *m_pSolver;
    unsigned m_nVars;
    unsigned m_nFrames;

    /// Inputs, by frame
    std::vector<abc::Vec_Int_t*> m_vInputs;
    /// Outputs, by frame
    std::vector<abc::Vec_Int_t*> m_vOutputs;

    /// All assumptions
    std::vector<int> m_Assumps;

    /**
     * Start of frame assumptions in m_Assumps
     * m_Assumps[i] is the start of assumptions of frame i in m_Assumps
     */
    std::vector<unsigned> m_FrameAssump;

    boost::dynamic_bitset<> *m_pEnabledAssumps;

    bool m_fWithAssump;
  
  
  public:
    Unroller(SatSolver &s, bool fWithAssump = false) : 
      m_pSolver (&s), m_nVars(0), m_nFrames(0),
      m_pEnabledAssumps(0), m_fWithAssump (fWithAssump)
    { newFrame (); }

    ~Unroller () { reset (NULL); }

    
    void setEnabledAssumps (boost::dynamic_bitset<> &v)
    { m_pEnabledAssumps = &v; }

    /** Reset everything */
    void reset (SatSolver *solver)
    {
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
      int *bgn = &m_Assumps[0] + m_FrameAssump.at (nFrame);
      int *end = &m_Assumps[0];
      if (nFrame == m_FrameAssump.size ())
        end += m_Assumps.size ();
      else
        end += m_FrameAssump.at (nFrame + 1);
      return std::make_pair (bgn, end);
    }
  
  
    unsigned frame () { return m_nFrames - 1; }
    
    void newFrame ()
    {
      m_nFrames++;
      m_vInputs.push_back (Vec_IntAlloc (16));
      m_vOutputs.push_back (Vec_IntAlloc (16));

      m_FrameAssump.push_back (m_Assumps.size ());
    }
    
    void addInput (int in) 
    { abc::Vec_IntPush (m_vInputs.at (frame ()), in); }

    int getInput (unsigned nFrame, int nNum)
    { return abc::Vec_IntEntry (m_vInputs.at (nFrame), nNum); }
  
    abc::Vec_Int_t *getInputs (unsigned nFrame) { return m_vInputs.at (nFrame); }  

    void addOutput (int out)
    { abc::Vec_IntPush (m_vOutputs.at (frame ()), out); }

    int getOutput (unsigned nFrame, int nNum)
    { return abc::Vec_IntEntry (m_vOutputs.at (nFrame), nNum); }

    abc::Vec_Int_t *getOutputs (unsigned nFrame) { return m_vOutputs.at (nFrame); }
    std::vector<abc::Vec_Int_t*> &getAllOutputs () { return m_vOutputs; }
    


    /** Add clause to solver */
    boost::tribool addClause (abc::lit* beg, abc::lit* end) 
    { return m_pSolver->addClause (beg, end); }
  
    boost::tribool addCnf (Cnf_Dat_t* pCnf)
    {
      boost::tribool res = true;
      for (int i = 0; i < pCnf->nClauses; ++i)
        res = res && addClause (pCnf->pClauses [i], pCnf->pClauses [i+1]);
      return res;
    }
    

    

    /** Add glue clauses between current Inputs and previous frame outputs */
    void glueOutIn ()
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
          
          // -- if known assumption, either add the clause or skip it
          // -- based on the value
          if (m_pEnabledAssumps && aLit < m_pEnabledAssumps->size ())
            {
              if (!m_pEnabledAssumps->test (aLit)) return;
            }
          else // unknown assumption, proceed as usual
            {
              addAssump (aLit);
              Lit[2] = lit_neg (aLit);
              litSz = 3;
            }
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

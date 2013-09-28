#ifndef _ITPSATSOLVER2_H_
#define _ITPSATSOLVER2_H_

#include "boost/noncopyable.hpp"
#include "boost/logic/tribool.hpp"

#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "AigUtils.h"

#include "sat/bsat/satSolver2.h"
#include "sat/bsat/satStore.h"

#include <vector>

namespace avy
{
  using namespace abc;
  
  typedef std::vector<lit> LitVector;
  
  
  /// Thin wrapper around interpolating sat solver
  class ItpSatSolver2 : boost::noncopyable
  {
  private:
    sat_solver2 *m_pSat;
    
    /// true if last result was trivial
    bool m_Trivial;

    /// current state
    boost::tribool m_State;

    std::vector<int> m_UnmrkdClauses;
    

  private:
    boost::tribool tbool (int v)
    {
      switch (v)
        {
        case l_False: return false;
        case l_True: return true;
        case l_Undef: return boost::tribool (boost::indeterminate);
        default: AVY_UNREACHABLE();
        }
    }
    
  public:
    /// create a solver with nParts partitions and nVars variables
    ItpSatSolver2 ( unsigned nVars) : m_pSat (0) 
    { reset (nVars); }
    
    ~ItpSatSolver2 ()
    {
      if (m_pSat) sat_solver2_delete (m_pSat);
      m_pSat = NULL;
    }

    /// reset and allocate nParts partitions and nVars variables
    void reset (unsigned nVars)
    {
      if (m_pSat) sat_solver2_delete (m_pSat);
      m_Trivial = false;
      m_State = boost::tribool (boost::indeterminate);
      m_pSat = sat_solver2_new ();
      AVY_ASSERT (m_pSat != NULL);

      sat_solver2_setnvars (m_pSat, nVars);
    }

    /// Mark currently unmarked clauses as belonging to partition nPart
    void markA ()
    { 
      BOOST_FOREACH (int h, m_UnmrkdClauses)
        clause2_set_partA (m_pSat, h, 1);
      
      m_UnmrkdClauses.clear ();
    }


    void reserve (unsigned nVars)
    { sat_solver2_setnvars (m_pSat, nVars); }
    

    /// add a clause
    bool addClause (lit* begin, lit* end)
    {
      m_Trivial = !sat_solver2_addclause (m_pSat, begin, end, -1); 
      LOG("sat", logs () << "NEW CLS: ";
          for (lit *it = begin; it != end; ++it)
            logs () << (lit_sign (*it) ? "-" : "") << lit_var (*it) << " ";

          logs () << "\n";);
      
      return !m_Trivial;
    }
    
    /// raw access to the sat solver
    sat_solver2* get () { return m_pSat; }
    
    /// true if the context is decided 
    bool isSolved () { return m_Trivial || m_State || !m_State; }

    /// decide context with assumptions
    boost::tribool solve (LitVector &assumptions, int maxSize = -1)
    {
      if (isTrivial ()) return false;
      if (!assumptions.empty ()) m_State = boost::tribool (boost::indeterminate);
      
      if (isSolved ()) return m_State;
      
      AVY_ASSERT (m_pSat != NULL);


      lit *beg = NULL;
      if (maxSize < 0) maxSize = assumptions.size ();
      if (maxSize > 0) beg = &assumptions[0];

      int RetValue;
      if (m_pSat->qtail != m_pSat->qhead)
        {
          RetValue = sat_solver2_simplify (m_pSat);
          AVY_ASSERT (RetValue != 0);
        }
      
      RetValue = sat_solver2_solve( m_pSat, beg, beg + assumptions.size (), 
                                    (ABC_INT64_T)10000000, (ABC_INT64_T)0, 
                                    (ABC_INT64_T)0, (ABC_INT64_T)0 );      

      
      m_State = tbool (RetValue);
      return m_State;
      
    }

    /// a pointer to the unsat core
    int core (int **out) { return sat_solver2_final (m_pSat, out); }
    
    /// decide current context
    boost::tribool solve ()
    {
      LitVector v;
      return solve (v);
    }

    bool isTrivial () { return m_Trivial; }
    

    /// Compute an interpolant. User provides the list of shared variables
    /// Variables can only be shared between adjacent partitions.
    /// fMcM == true for McMillan, and false for McMillan'
    //Aig_Man_t* getInterpolant (std::vector<Vec_Int_t*> &vSharedVars, bool fMcM=true);
  };
  
}



#endif /* _ITPSATSOLVER2_H_ */

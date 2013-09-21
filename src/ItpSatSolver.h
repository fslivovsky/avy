#ifndef _ITPSATSOLVER_H_
#define _ITPSATSOLVER_H_

#include "boost/noncopyable.hpp"
#include "boost/logic/tribool.hpp"

#include "avy/util/AvyDebug.h"
#include "AigUtils.h"

#include "sat/bsat/satSolver.h"

namespace avy
{
  using namespace abc;
  
  /// Thin wrapper around interpolating sat solver
  class ItpSatSolver : boost::noncopyable
  {
  private:
    sat_solver *m_pSat;
    
    /// true if last result was trivial
    bool m_Trivial;

    /// number of partitions
    unsigned m_nParts;

    /// current state
    boost::tribool m_State;

  private:
    boost::tribool tbool (int v)
    {
      switch (v)
        {
        case l_False: return false;
        case l_True: return true;
        case l_Undef: return boost::indeterminate;
        default: AVY_UNREACHABLE();
        }
    }
    
  public:
    /// create a solver with nParts partitions and nVars variables
    ItpSatSolver (unsigned nParts, unsigned nVars) : m_pSat (0) { reset (nParts, nVars); }
    
    ~ItpSatSolver ()
    {
      if (m_pSat) sat_solver_delete (m_pSat);
      m_pSat = NULL;
    }

    /// reset and allocate nParts partitions and nVars variables
    void reset (unsigned nParts, unsigned nVars)
    {
      if (m_pSat) sat_solver_delete (m_pSat);
      m_nParts = nParts;
      m_Trivial = false;
      m_State = boost::indeterminate;
      m_pSat = sat_solver_new ();
      sat_solver_store_alloc (m_pSat, nParts);
      sat_solver_setnvars (m_pSat, nVars);
    }

    /// Mark currently unmarked clauses as belonging to partition nPart
    void markParitition (unsigned nPart)
    { sat_solver_store_mark_clauses_a (m_pSat, nPart); }

    /// add a clause, and offset the VARIABLES of the clause by nVarsPlus
    bool addClause (lit* begin, lit* end, unsigned nVarsPlus=0)
    {
      if (nVarsPlus > 0) for (lit *it = begin; it != end; ++it) *it += 2*nVarsPlus;
      m_Trivial = !sat_solver_addclause (m_pSat, begin, end); 
      if (nVarsPlus > 0) for (lit *it = begin; it != end; ++it) *it -= 2*nVarsPlus;
      return !m_Trivial;
    }
    
    void dumpCnf (std::string fname) 
    { sat_solver_store_write (m_pSat, const_cast<char*>(fname.c_str ())); }
    

    /// raw access to the sat solver
    sat_solver* get () { return m_pSat; }
    
    /// true if the context is decided 
    bool isSolved () { return m_Trivial || m_State || !m_State; }
    
    /// decide current context
    boost::tribool solve ()
    {
      if (isTrivial ()) return false;
      if (isSolved ()) return m_State;
      
      AVY_ASSERT (m_pSat != NULL);
      
      sat_solver_store_mark_roots( m_pSat );
      int RetValue = sat_solver_solve( m_pSat, NULL,  NULL, 
                                       (ABC_INT64_T)10000000, (ABC_INT64_T)0, 
                                       (ABC_INT64_T)0, (ABC_INT64_T)0 );
      
      m_State = tbool (RetValue);
      return m_State;
    }
    bool isTrivial () { return m_Trivial; }
    

    /// Compute an interpolant. User provides the list of shared variables
    /// Variables can only be shared between adjacent partitions.
    /// fMcM == true for McMillan, and false for McMillan'
    // XXX Why is vSharedVars not Vec_Vec_t? It would make it easier to grow
    Aig_Man_t* getInterpolant (Vec_Int_t** vSharedVars, bool fMcM=true);
  };
  
}



#endif /* _ITPSATSOLVER_H_ */

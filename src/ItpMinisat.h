#ifndef _ITP_MINISAT_H_
#define _ITP_MINISAT_H_

#include "boost/noncopyable.hpp"
#include "boost/logic/tribool.hpp"

#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "AigUtils.h"

#include "core/Solver.h"

#include <vector>

namespace avy
{
  using namespace abc;

  typedef std::vector<lit> LitVector;
  
  
  /// Thin wrapper around interpolating sat solver
  class ItpMinisat : boost::noncopyable
  {
  private:
    ::Minisat::Solver *m_pSat;

    /// true if last result was trivial
    bool m_Trivial;

    /// number of partitions
    unsigned m_nParts;

    /// current state
    boost::tribool m_State;

    
  public:
    /// create a solver with nParts partitions and nVars variables
    ItpMinisat (unsigned nParts, unsigned nVars) : m_pSat (0)
    { reset (nParts, nVars); }
    
    ~ItpMinisat ()
    {
      if (m_pSat) delete m_pSat;
      m_pSat = NULL;
    }

    /// reset and allocate nParts partitions and nVars variables
    void reset (unsigned nParts, unsigned nVars)
    {
      AVY_ASSERT (nParts >= 2 && "require at least 2 partitions");
      if (m_pSat) delete m_pSat;
      m_nParts = nParts;
      m_Trivial = false;
      m_State = boost::tribool (boost::indeterminate);
      m_pSat = new ::Minisat::Solver();
      m_pSat->setCurrentPart(1);
    }

    /// Mark currently unmarked clauses as belonging to partition nPart
    void markPartition (unsigned nPart)
    { 
      AVY_ASSERT (nPart > 1 && nPart <= m_nParts);
      m_pSat->setCurrentPart(nPart);
    }
    
    void reserve (int nVars)
    { while (m_pSat->nVars () < nVars) m_pSat->newVar (); }

    
    bool addUnit (int unit)
    {
      ::Minisat::Lit p = ::Minisat::toLit (unit);
      LOG ("sat", logs () << "UNT: "
           << (::Minisat::sign (p) ? "-" : "")
           << (::Minisat::var (p)) << " ";);
      m_Trivial = !m_pSat->addClause (p);
      return m_Trivial;
    }

    bool addClause (int* bgn, int* end)
    {
      LOG("sat", logs () << "NEW CLS: ";);
      ::Minisat::vec< ::Minisat::Lit> cls;
      cls.capacity (end-bgn);
      for (int* it = bgn; it != end; ++it)
        {
          ::Minisat::Lit p = ::Minisat::toLit (*it);
          cls.push (p);


          LOG("sat", logs () << (::Minisat::sign (p) ? "-" : "")
              << (::Minisat::var (p)) << " ";);
        }
      LOG("sat", logs () << "\n" << std::flush;);
      
      m_Trivial = !m_pSat->addClause (cls);
      return !m_Trivial;
    }
    
    void dumpCnf (std::string fname)
    { m_pSat->toDimacs(const_cast<char*>(fname.c_str ()), ::Minisat::vec< ::Minisat::Lit>()); }


    /// raw access to the sat solver
    ::Minisat::Solver* get () { return m_pSat; }
    
    /// true if the context is decided 
    bool isSolved () { return m_Trivial || m_State || !m_State; }

    /// decide context with assumptions
    //boost::tribool solve (LitVector &assumptions, int maxSize = -1)

    /// a pointer to the unsat core
    //int core (int **out) { return sat_solver_final (m_pSat, out); }
    
    /// decide current context
    boost::tribool solve () { return m_pSat->solve (); }

    bool isTrivial () { return m_Trivial; }
    
    void setFrozen (int v, bool p) { }//m_pSat->setFrozen (v, p); }

    /// Compute an interpolant. User provides the list of shared variables
    /// Variables can only be shared between adjacent partitions.
    /// fMcM == true for McMillan, and false for McMillan'
    Aig_Man_t* getInterpolant (std::vector<int> &vVarToId, int nNumOfVars);
    
  };
  
}



#endif /* _ITPSATSOLVER_H_ */

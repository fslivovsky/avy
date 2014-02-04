#ifndef _MINISAT_H_
#define _MINISAT_H_

#include "simp/SimpSolver.h"

namespace avy
{
  class Minisat
  {
    ::Minisat::SimpSolver *m_sat;
    bool m_Trivial;

    std::vector<int> m_core;
    
  public:
    Minisat (unsigned nVars) : m_sat(NULL), m_Trivial(false)
    { reset (nVars); }

    virtual ~Minisat () 
    { 
      if (m_sat) delete m_sat; 
    }

    void reset (int nVars)
    {
      m_core.clear ();
      if (m_sat) delete m_sat;
      m_sat = new ::Minisat::SimpSolver ();      
      reserve (nVars);
    }

    void reserve (int nVars)
    { while (m_sat->nVars () < nVars) m_sat->newVar (); }
    
    
    bool addUnit (int unit) 
    { 
      ::Minisat::Lit p = ::Minisat::toLit (unit);
      LOG ("sat", logs () << "UNT: "
           << (::Minisat::sign (p) ? "-" : "") 
           << (::Minisat::var (p)) << " ";);
      m_Trivial = !m_sat->addClause (p); 
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
      
      m_Trivial = !m_sat->addClause (cls);
      return !m_Trivial;
    }
    
    boost::tribool solve (std::vector<int> &assumptions, int maxSize = -1)
    {
      if (m_Trivial) return false;

      if (!m_sat->okay ()) return false;
      
      ::Minisat::vec< ::Minisat::Lit> massmp;
      massmp.capacity (assumptions.size ());
      int max = assumptions.size ();
      if (maxSize >= 0 && maxSize < max) max = maxSize;
      
      for (unsigned i = 0; i < max; ++i) 
        { 
          ::Minisat::Lit p = ::Minisat::toLit (assumptions [i]);
          massmp.push (p);
          LOG ("sat", logs () << "ASM: " << (::Minisat::sign (p) ? "-" : "") 
               << (::Minisat::var (p)) << " " << "\n";);
        }
      return m_sat->solve (massmp);
    }
    
    int core (int **out)
    {
      m_core.clear ();
      m_core.resize (m_sat->conflict.size ());
      for (unsigned i = 0 ; i < m_sat->conflict.size (); i++)
        m_core[i] = m_sat->conflict[i].x;

      *out = &m_core[0];
      return m_core.size ();
    }
    
    boost::tribool solve () { return m_sat->solve (); }
    
    bool isTrivial () { return m_Trivial; }
    
    void setFrozen (int v, bool p) { m_sat->setFrozen (v, p); }
    
    
    
    
  };
  
}

#undef l_True
#undef l_False
#undef l_Undef

#endif /* _MINISAT_H_ */

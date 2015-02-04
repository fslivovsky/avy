#ifndef _GLUCOSE_H_
#define _GLUCOSE_H_

#include "glucose/simp/SimpSolver.h"
#include "avy/Util/Stats.h"

namespace avy
{
  class Glucose
  {
    ::Glucose::SimpSolver *m_sat;
    bool m_Trivial;
    bool m_Simplifier;
    bool m_Incremental;

    std::vector<int> m_core;
    
    
    boost::tribool tobool (::Glucose::lbool v)
    {
      boost::tribool r (boost::indeterminate);
      if (v == ::Glucose::lbool ((uint8_t)0)) r = true;
      else if (v == ::Glucose::lbool ((uint8_t)1)) r = false;
      return r;
    }
    
  public:
    Glucose (unsigned nVars, bool simp = true, bool inc = false) :
      m_sat(NULL), m_Trivial(false), m_Simplifier (simp), m_Incremental (inc)
    { reset (nVars); }

    virtual ~Glucose () { if (m_sat) delete m_sat; }

    void reset (int nVars)
    {
      m_core.clear ();
      if (m_sat) delete m_sat;
      m_sat = new ::Glucose::SimpSolver ();
      
      m_sat->proofLogging(false);
      m_sat->setIncrementalMode ();
      reserve (nVars);
    }

    void reserve (int nVars)
    { while (m_sat->nVars () < nVars) m_sat->newVar (); }
    
    
    bool addUnit (int unit) 
    { 
      ::Glucose::Lit p = ::Glucose::toLit (unit);
      LOG ("sat", logs () << "UNT: "
           << (::Glucose::sign (p) ? "-" : "") 
           << (::Glucose::var (p)) << " ";);
      m_Trivial = !m_sat->addClause (p); 
      return m_Trivial;
    }

    bool addClause (int* bgn, int* end)
    {
      LOG("sat", logs () << "NEW CLS: ";);
      ::Glucose::vec< ::Glucose::Lit> cls;
      cls.capacity (end-bgn);
      for (int* it = bgn; it != end; ++it)
        {
          ::Glucose::Lit p = ::Glucose::toLit (*it);
          cls.push (p);

          
          LOG("sat", logs () << (::Glucose::sign (p) ? "-" : "") 
              << (::Glucose::var (p)) << " ";);
        }
      LOG("sat", logs () << "\n" << std::flush;);
      
      m_Trivial = !m_sat->addClause (cls);
      return !m_Trivial;
    }
    
    void dumpCnf (std::string fname)
    { 
      
      ::Glucose::vec< ::Glucose::Lit> v;
      m_sat->toDimacs(const_cast<char*>(fname.c_str ()), v); 
    }


    boost::tribool solve (std::vector<int> &assumptions, int maxSize = -1)
    {
      ScoppedStats __stats__("Glucose_solve");
      if (m_Trivial) return false;

      if (!m_sat->okay ()) return false;
      
      ::Glucose::vec< ::Glucose::Lit> massmp;
      massmp.capacity (assumptions.size ());
      int max = assumptions.size ();
      if (maxSize >= 0 && maxSize < max) max = maxSize;
      
      for (unsigned i = 0; i < max; ++i) 
        { 
          ::Glucose::Lit p = ::Glucose::toLit (assumptions [i]);
          massmp.push (p);
          LOG ("sat", logs () << "ASM: " << (::Glucose::sign (p) ? "-" : "") 
               << (::Glucose::var (p)) << " " << "\n";);
        }
      return m_sat->solve (massmp, m_Simplifier, !m_Simplifier);
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
    
    boost::tribool solve () { return m_sat->solve (m_Simplifier, !m_Simplifier); }
    
    bool isTrivial () { return m_Trivial; }
    
    void setFrozen (int v, bool p) 
    { 
      m_sat->setFrozen (v, p); 
      m_sat->setSelector (v, p);
    }
    
    boost::tribool getVarVal(int v)
    {
      ::Glucose::Var x = v;
      return tobool (m_sat->modelValue(x));
    }

    void markPartition(int nPart) {}

  };
    
}

#undef l_True
#undef l_False
#undef l_Undef

#endif /* _GLUCOSE_H_ */

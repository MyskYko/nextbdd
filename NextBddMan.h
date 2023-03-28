#ifndef NEXT_BDD_MAN_H
#define NEXT_BDD_MAN_H

#include <vector>
#include <cmath>
#include <iostream>
#include <iomanip>

#include "NextBddTypes.h"

namespace NextBdd {

  struct Param {
    int nObjsMaxLog = 25;
    int nObjsAllocLog = 20;
    int nUniqueLog = 10;
    double UniqueDensity = 4;
    int nCacheLog = 15;
    int nCacheMaxLog = 20;
    std::vector<var> *pVar2Level = NULL;
    bool fCountOnes = false;
  };

  class Man {
  public:
    Man(int nVars, Param p, int nVerbose);
    ~Man();

    bvar CountNodes();
    bvar CountNodes(std::vector<lit> const &vLits);
    void PrintStats();

    lit And(lit x, lit y);

  private:
    var nVars;
    std::vector<var> Var2Level;
    std::vector<var> Level2Var;

    bvar nObjs;
    bvar nObjsAlloc;
    bvar nObjsMax;
    bvar RemovedHead;
    std::vector<var> vVars;
    std::vector<lit> vObjs;
    std::vector<bvar> vNexts;
    std::vector<bool> vMarks;
    std::vector<double> vOneCounts;
    std::vector<ref> vRefs;
    std::vector<edge> vEdges;

    std::vector<std::vector<bvar> > vvUnique;
    std::vector<uniq> vUniqueMasks;
    std::vector<bvar> vUniqueCounts;
    std::vector<bvar> vUniqueTholds;

    int nGbc;
    bvar nReo;
    double MaxGrowth;
    bool fReoVerbose;

    int nVerbose;

    inline lit UniqueCreateInt(var v, lit x1, lit x0);
    inline lit UniqueCreate(var v, lit x1, lit x0);
    inline void ResizeUnique(var v);
    inline bool Resize();
    inline bool Gbc();

    lit And_rec(lit x, lit y);

    bvar CountNodes_rec(lit x);

    void SetMark_rec(lit x);
    void ResetMark_rec(lit x);

  public:
    inline lit Const0() const { return (lit)0; }
    inline lit Const1() const { return (lit)1; }
    inline lit IthVar(var v) const { return Bvar2Lit((bvar)v + 1); }

    inline lit LitRegular(lit x) const { return x & ~(lit)1; }
    inline lit LitIrregular(lit x) const { return x | (lit)1; }
    inline lit LitNot(lit x) const { return x ^ (lit)1; }
    inline lit LitNotCond(lit x, bool c) const { return x ^ (lit)c; }

    inline bool LitIsCompl(lit x) const { return x & (lit)1; }
    inline var Var(lit x) const { return vVars[Lit2Bvar(x)]; }
    inline var Level(lit x) const { return Var2Level[Var(x)]; }
    inline lit Then(lit x) const { return LitNotCond(vObjs[LitRegular(x)], LitIsCompl(x)); }
    inline lit Else(lit x) const { return LitNotCond(vObjs[LitIrregular(x)], LitIsCompl(x)); }
    inline double OneCount(lit x) const {
      if(vOneCounts.empty())
        throw std::logic_error("fCountOnes was not set");
      if(LitIsCompl(x))
        return std::pow(2.0, nVars) - vOneCounts[Lit2Bvar(x)];
      return vOneCounts[Lit2Bvar(x)];
    }

    inline ref Ref(lit x) const { return vRefs[Lit2Bvar(x)]; }
    inline void IncRef(lit x) { if(!vRefs.empty() && Ref(x) != RefMax()) vRefs[Lit2Bvar(x)]++; }
    inline void DecRef(lit x) { if(!vRefs.empty() && Ref(x) != RefMax()) vRefs[Lit2Bvar(x)]--; }

  private:
    inline bool Mark(lit x) const { return vMarks[Lit2Bvar(x)]; }
    inline edge Edge(lit x) const { return vEdges[Lit2Bvar(x)]; }

    inline void SetMark(lit x) { vMarks[Lit2Bvar(x)] = true; }
    inline void ResetMark(lit x) { vMarks[Lit2Bvar(x)] = false; }
    inline void IncEdge(lit x) { vEdges[Lit2Bvar(x)]++; }
    inline void DecEdge(lit x) { vEdges[Lit2Bvar(x)]--; }

    inline lit Bvar2Lit(bvar a) const { return (lit)a << 1; }
    inline lit Bvar2Lit(bvar a, bool c) const { return ((lit)a << 1) ^ (lit)c; }
    inline bvar Lit2Bvar(lit x) const { return (bvar)(x >> 1); }

    inline var VarOfBvar(bvar a) const { return vVars[a]; }
    inline lit ThenOfBvar(bvar a) const { return vObjs[Bvar2Lit(a)]; }
    inline lit ElseOfBvar(bvar a) const { return vObjs[Bvar2Lit(a, true)]; }
    inline bool MarkOfBvar(bvar a) const { return vMarks[a]; }
    inline ref RefOfBvar(bvar a) const { return vRefs[a]; }
    inline edge EdgeOfBvar(bvar a) const { return vEdges[a]; }

    inline void SetVarOfBvar(bvar a, var v) { vVars[a] = v; }
    inline void SetThenOfBvar(bvar a, lit x) { vObjs[Bvar2Lit(a)] = x; }
    inline void SetElseOfBvar(bvar a, lit x) { vObjs[Bvar2Lit(a, true)] = x; }
    inline void SetMarkOfBvar(bvar a) { vMarks[a] = true; }
    inline void ResetMarkOfBvar(bvar a) { vMarks[a] = false; }

    inline void RemoveBvar(bvar a) {
      var v = VarOfBvar(a);
      SetVarOfBvar(a, VarMax());
      std::vector<bvar>::iterator q = vvUnique[v].begin() + (UniqHash(ThenOfBvar(a), ElseOfBvar(a)) & vUniqueMasks[v]);
      for(; *q; q = vNexts.begin() + *q)
        if(*q == a)
          break;
      bvar next = vNexts[*q];
      vNexts[*q] = RemovedHead;
      RemovedHead = *q;
      *q = next;
      vUniqueCounts[v]--;
    }
  };

  void Man::SetMark_rec(lit x) {
    if(x < 2 || Mark(x))
      return;
    SetMark(x);
    SetMark_rec(Then(x));
    SetMark_rec(Else(x));
  }
  void Man::ResetMark_rec(lit x) {
    if(x < 2 || !Mark(x))
      return;
    ResetMark(x);
    ResetMark_rec(Then(x));
    ResetMark_rec(Else(x));
  }

  Man::Man(int nVars, Param p, int nVerbose): nVars(nVars), nVerbose(nVerbose) {
    // parameter sanity check
    if(p.nObjsMaxLog < p.nObjsAllocLog)
      throw std::invalid_argument("nObjsMax must not be smaller than nObjsAlloc");
    if(nVars >= (int)VarMax())
      throw std::length_error("Memout (nVars) in init");
    lit nObjsMaxLit = (lit)1 << p.nObjsMaxLog;
    if(!nObjsMaxLit)
      throw std::length_error("Memout (nObjsMax) in init");
    if(nObjsMaxLit > (lit)BvarMax())
      nObjsMax = BvarMax();
    else
      nObjsMax = (bvar)nObjsMaxLit;
    lit nObjsAllocLit = (lit)1 << p.nObjsAllocLog;
    if(!nObjsAllocLit)
      throw std::length_error("Memout (nObjsAlloc) in init");
    if(nObjsAllocLit > (lit)BvarMax())
      nObjsAlloc = BvarMax();
    else
      nObjsAlloc = (bvar)nObjsAllocLit;
    if(nObjsAlloc <= (bvar)nVars)
      throw std::invalid_argument("nObjsAlloc must be larger than nVars");
    uniq nUnique = (uniq)1 << p.nUniqueLog;
    if(!nUnique)
      throw std::length_error("Memout (nUnique) in init");
    // allocation
    if(nVerbose)
      std::cout << "Allocating " << nObjsAlloc << " nodes and " << nVars << " x " << nUnique << " unique table entries" << std::endl;
    vVars.resize(nObjsAlloc);
    vObjs.resize((lit)nObjsAlloc * 2);
    vNexts.resize(nObjsAlloc);
    vMarks.resize(nObjsAlloc);
    vvUnique.resize(nVars);
    vUniqueMasks.resize(nVars);
    vUniqueCounts.resize(nVars);
    vUniqueTholds.resize(nVars);
    for(var v = 0; v < nVars; v++) {
      vvUnique[v].resize(nUnique);
      vUniqueMasks[v] = nUnique - 1;
      if(nUnique * p.UniqueDensity > (double)BvarMax())
        vUniqueTholds[v] = BvarMax();
      else
        vUniqueTholds[v] = (bvar)(nUnique * p.UniqueDensity);
    }
    if(p.fCountOnes) {
      if(nVars > 1023)
        throw std::length_error("nVars must be less than 1024 to count ones");
      vOneCounts.resize(nObjsAlloc);
    }
    // create nodes for variables
    nObjs = 1;
    vVars[0] = VarMax();
    for(var v = 0; v < nVars; v++)
      UniqueCreateInt(v, 1, 0);
    // set up variable order
    Var2Level.resize(nVars);
    Level2Var.resize(nVars);
    for(var v = 0; v < nVars; v++) {
      if(p.pVar2Level)
        Var2Level[v] = (*p.pVar2Level)[v];
      else
        Var2Level[v] = v;
      Level2Var[Var2Level[v]] = v;
    }
    // set other parameters
    RemovedHead = 0;
    nGbc = 0;
    nReo = BvarMax();
    MaxGrowth = 0;
    fReoVerbose = false;
  }
  Man::~Man() {
    if(nVerbose) {
      std::cout << "Free " << nObjsAlloc << " nodes (" << nObjs << " live nodes)" << std::endl;
      std::cout << "Free {";
      std::string delim;
      for(var v = 0; v < nVars; v++) {
        std::cout << delim << vvUnique[v].size();
        delim = ", ";
      }
      std::cout << "} unique table entries" << std::endl;
      if(!vRefs.empty())
        std::cout << "Free " << vRefs.size() << " refs" << std::endl;
    }
    //delete cache;
  }

  bvar Man::CountNodes_rec(lit x) {
    if(x < 2 || Mark(x))
      return 0;
    SetMark(x);
    return 1 + CountNodes_rec(Then(x)) + CountNodes_rec(Else(x));
  }
  bvar Man::CountNodes() {
    bvar count = 0;
    if(!vEdges.empty()) {
      for(bvar a = 1; a < nObjs; a++)
        if(EdgeOfBvar(a))
          count++;
      return count;
    }
    for(bvar a = 1; a <= (bvar)nVars; a++) {
      count++;
      SetMarkOfBvar(a);
    }
    for(bvar a = (bvar)nVars + 1; a < nObjs; a++)
      if(RefOfBvar(a))
        count += CountNodes_rec(Bvar2Lit(a));
    for(bvar a = 1; a <= (bvar)nVars; a++)
      ResetMarkOfBvar(a);
    for(bvar a = (bvar)nVars + 1; a < nObjs; a++)
      if(RefOfBvar(a))
        ResetMark_rec(Bvar2Lit(a));
    return count;
  }
  bvar Man::CountNodes(std::vector<lit> const &vLits) {
    bvar count = 0;
    for(size_t i = 0; i < vLits.size(); i++)
      count += CountNodes_rec(vLits[i]);
    for(size_t i = 0; i < vLits.size(); i++)
      ResetMark_rec(vLits[i]);
    return count + 1;
  }

  void Man::PrintStats() {
    bvar nRemoved = 0;
    bvar a = RemovedHead;
    while(a) {
      nRemoved++;
      a = vNexts[a];
    }
    if(!vRefs.empty())
      std::cout << "ref: " << std::setw(10) << CountNodes() << ", ";
    std::cout << "used: " << std::setw(10) << nObjs << ", "
              << "live: " << std::setw(10) << nObjs - nRemoved << ", "
              << "dead: " << std::setw(10) << nRemoved << ", "
              << "alloc: " << std::setw(10) << nObjsAlloc
              << std::endl;
  }

  inline lit Man::UniqueCreateInt(var v, lit x1, lit x0) {
    std::vector<bvar>::iterator p, q;
    p = q = vvUnique[v].begin() + (UniqHash(x1, x0) & vUniqueMasks[v]);
    for(; *q; q = vNexts.begin() + *q)
      if(VarOfBvar(*q) == v && ThenOfBvar(*q) == x1 && ElseOfBvar(*q) == x0)
        return Bvar2Lit(*q);
    bvar next = *p;
    if(nObjs < nObjsAlloc)
      *p = nObjs++;
    else if(RemovedHead)
      *p = RemovedHead, RemovedHead = vNexts[*p];
    else
      return LitMax();
    SetVarOfBvar(*p, v);
    SetThenOfBvar(*p, x1);
    SetElseOfBvar(*p, x0);
    vNexts[*p] = next;
    if(!vOneCounts.empty())
      vOneCounts[*p] = OneCount(x1) / 2 + OneCount(x0) / 2;
    if(nVerbose >= 3) {
      std::cout << "Create node " << std::setw(10) << *p << ": "
                << "Var = " << std::setw(6) << v << ", "
                << "Then = " << std::setw(10) << x1 << ", "
                << "Else = " << std::setw(10) << x0;
      if(!vOneCounts.empty())
        std::cout << ", Ones = " << std::setw(10) << vOneCounts[*q];
      std::cout << std::endl;
    }
    vUniqueCounts[v]++;
    if(vUniqueCounts[v] > vUniqueTholds[v]) {
      bvar a = *p;
      ResizeUnique(v);
      return Bvar2Lit(a);
    }
    return Bvar2Lit(*p);
  }
  inline lit Man::UniqueCreate(var v, lit x1, lit x0) {
    if(x1 == x0)
      return x1;
    lit x;
    while(true) {
      if(!LitIsCompl(x0))
        x = UniqueCreateInt(v, x1, x0);
      else
        x = UniqueCreateInt(v, LitNot(x1), LitNot(x0));
      if(x == LitMax()) {
        bool fRemoved = false;
        if(nGbc > 1)
          fRemoved = Gbc();
        if(!Resize() && !fRemoved && (nGbc != 1 || !Gbc()))
          throw std::length_error("Memout (node)");
      } else
        break;
    }
    return LitIsCompl(x0)? LitNot(x): x;
  }

  inline void Man::ResizeUnique(var v) {
    uniq nUnique, nUniqueOld;
    nUnique = nUniqueOld = vvUnique[v].size();
    nUnique <<= 1;
    if(!nUnique) {
      vUniqueTholds[v] = BvarMax();
      return;
    }
    if(nVerbose >= 2)
      std::cout << "Reallocating " << nUnique << " unique table entries for Var " << v << std::endl;
    vvUnique[v].resize(nUnique);
    vUniqueMasks[v] = nUnique - 1;
    for(uniq i = 0; i < nUniqueOld; i++) {
      std::vector<bvar>::iterator q, tail, tail1, tail2;
      q = tail1 = vvUnique[v].begin() + i;
      tail2 = q + nUniqueOld;
      while(*q) {
        uniq hash = UniqHash(ThenOfBvar(*q), ElseOfBvar(*q)) & vUniqueMasks[v];
        if(hash == i)
          tail = tail1;
        else
          tail = tail2;
        if(tail != q)
          *tail = *q, *q = 0;
        q = vNexts.begin() + *tail;
        if(tail == tail1)
          tail1 = q;
        else
          tail2 = q;
      }
    }
    vUniqueTholds[v] <<= 1;
    if((lit)vUniqueTholds[v] > (lit)BvarMax())
      vUniqueTholds[v] = BvarMax();
  }
  bool Man::Resize() {
    if(nObjsAlloc == nObjsMax)
      return false;
    lit nObjsAllocLit = (lit)nObjsAlloc << 1;
    if(nObjsAllocLit > (lit)BvarMax())
      nObjsAlloc = BvarMax();
    else
      nObjsAlloc = (bvar)nObjsAllocLit;
    if(nVerbose >= 2)
      std::cout << "Reallocating " << nObjsAlloc << " nodes" << std::endl;
    vVars.resize(nObjsAlloc);
    vObjs.resize((lit)nObjsAlloc * 2);
    vNexts.resize(nObjsAlloc);
    vMarks.resize(nObjsAlloc);
    if(!vRefs.empty())
      vRefs.resize(nObjsAlloc);
    if(!vEdges.empty())
      vEdges.resize(nObjsAlloc);
    if(!vOneCounts.empty())
      vOneCounts.resize(nObjsAlloc);
    return true;
  }
  inline bool Man::Gbc() {
    if(nVerbose >= 2)
      std::cout << "Garbage collect" << std::endl;
    if(!vEdges.empty()) {
      for(bvar a = (bvar)nVars + 1; a < nObjs; a++)
        if(!EdgeOfBvar(a) && VarOfBvar(a) != VarMax())
          RemoveBvar(a);
    } else {
      for(bvar a = (bvar)nVars + 1; a < nObjs; a++)
        if(RefOfBvar(a))
          SetMark_rec(Bvar2Lit(a));
      for(bvar a = (bvar)nVars + 1; a < nObjs; a++)
        if(!MarkOfBvar(a) && VarOfBvar(a) != VarMax())
          RemoveBvar(a);
      for(bvar a = (bvar)nVars + 1; a < nObjs; a++)
        if(RefOfBvar(a))
          ResetMark_rec(Bvar2Lit(a));
    }
    // CacheClear();
    return RemovedHead;
  }

  lit Man::And(lit x, lit y) {
    // if(nObjs > nReo) {
    //   Reorder(fReoVerbose);
    //   while(nReo < nObjs) {
    //     nReo <<= 1;
    //     if((size)nReo > (size)BvarMax()) {
    //       nReo = BvarMax();
    //     }
    //   }
    // }
    return And_rec(x, y);
  }
  lit Man::And_rec(lit x, lit y) {
    if(x == 0 || y == 1)
      return x;
    if(x == 1 || y == 0)
      return y;
    if(Lit2Bvar(x) == Lit2Bvar(y))
      return (x == y)? x: 0;
    if(x > y)
      std::swap(x, y);
    lit z;
    // lit z = CacheLookup(x, y);
    // if(z != LitMax()) {
    //   return z;
    // }
    var v;
    lit x0, x1, y0, y1;
    if(Level(x) < Level(y))
      v = Var(x), x1 = Then(x), x0 = Else(x), y0 = y1 = y;
    else if(Level(x) > Level(y))
      v = Var(y), x0 = x1 = x, y1 = Then(y), y0 = Else(y);
    else
      v = Var(x), x1 = Then(x), x0 = Else(x), y1 = Then(y), y0 = Else(y);
    lit z1 = And_rec(x1, y1);
    IncRef(z1);
    lit z0 = And_rec(x0, y0);
    IncRef(z0);
    z = UniqueCreate(v, z1, z0);
    DecRef(z1);
    DecRef(z0);
    // CacheInsert(x, y, z);
    return z;
  }

}

#endif

#include "aig.hpp"
#include "NextBdd.h"

#include <map>
#include <stack>

using namespace std;

using namespace NextBdd;

int main(int argc, char **argv) {
  aigman aig(argv[1]);
  aig.supportfanouts();
  Param p;

  p.nObjsAllocLog = ceil(log2(aig.nPis)) + 1;
  p.nUniqueSizeLog = 0;
  p.nCacheSizeLog = 10;
  p.nGbc = 2;

  p.nReo = 100;
  // p.fReoVerbose = 1;
  // p.nVerbose = 2;

  Man man(aig.nPis, p);
  vector<lit> outputs;
  vector<int> vCounts(aig.nObjs);
  for(int i = aig.nPis + 1; i < aig.nObjs; i++)
    vCounts[i] = aig.vvFanouts[i].size();
  vector<lit> nodes(aig.nObjs);
  nodes[0] = man.Const0();
  for(int i = 0; i < aig.nPis; i++)
    nodes[i + 1] = man.IthVar(i);
  for(int i = aig.nPis + 1; i < aig.nObjs; i++) {
    int i0 = aig.vObjs[i + i] >> 1;
    int i1 = aig.vObjs[i + i + 1] >> 1;
    bool c0 = aig.vObjs[i + i] & 1;
    bool c1 = aig.vObjs[i + i + 1] & 1;
    nodes[i] = man.And(man.LitNotCond(nodes[i0], c0), man.LitNotCond(nodes[i1], c1));
    man.IncRef(nodes[i]);
    vCounts[i0]--;
    if(!vCounts[i0])
      man.DecRef(nodes[i0]);
    vCounts[i1]--;
    if(!vCounts[i1])
      man.DecRef(nodes[i1]);
  }
  for(int i = 0; i < aig.nPos; i++) {
    int i0 = aig.vPos[i] >> 1;
    bool c0 = aig.vPos[i] & 1;
    outputs.push_back(man.LitNotCond(nodes[i0], c0));
  }

  // man.PrintStats();
  // man.SetRef(outputs);
  // man.Gbc();
  // man.Reorder();
  // man.PrintStats();

  std::cout << man.CountNodes(outputs) << std::endl;

  int nPis = aig.nPis;
  aig.clear();
  aig.nPis = nPis;
  aig.nObjs = aig.nPis + 1;
  aig.vObjs.resize(aig.nObjs * 2);
  map<bvar, int> values;
  values[0] = 0;
  for(size_t i = 0; i < outputs.size(); i++) {
    bvar o = man.Lit2Bvar(outputs[i]);
    if(values.count(o))
      continue;
    stack<bvar> bvars;
    bvars.push(o);
    while(!bvars.empty()) {
      bvar a = bvars.top();
      bvar b = man.Lit2Bvar(man.ThenOfBvar(a));
      if(b && !values.count(b)) {
        bvars.push(b);
        continue;
      }
      bvar c = man.Lit2Bvar(man.ElseOfBvar(a));
      if(c && !values.count(c)) {
        bvars.push(c);
        continue;
      }
      int v = ((int)man.VarOfBvar(a) + 1) << 1;
      int p = values[b] ^ (int)man.LitIsCompl(man.ThenOfBvar(a));
      int q = values[c];
      int s = aig.newgate(v, p) << 1;
      int t = aig.newgate(v ^ 1, q) << 1;
      int r = (aig.newgate(s ^ 1, t ^ 1) << 1) ^ 1;
      values[a] = r;
      bvars.pop();
    }
  }
  for(size_t i = 0; i < outputs.size(); i++) {
    int r = values[man.Lit2Bvar(outputs[i])] ^ man.LitIsCompl(outputs[i]);
    aig.vPos.push_back(r);
    aig.nPos++;
  }
  aig.write("tmp.aig");

  return 0;
}

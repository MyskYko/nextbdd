#include "aig.hpp"
#include "NextBddMan.h"

using namespace std;

using namespace NextBdd;

int main(int argc, char **argv) {
  aigman aig(argv[1]);
  aig.supportfanouts();
  Param p;
  Man man(aig.nPis, p, 3);
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
  man.PrintStats();
  std::cout << "node count: " << man.CountNodes(outputs) << std::endl;
  return 0;
}

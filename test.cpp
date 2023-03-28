#include "NextBddMan.h"

using namespace NextBdd;

int main() {
  Param p;
  Man man(100, p, 3);
  man.PrintStats();
  return 0;
}

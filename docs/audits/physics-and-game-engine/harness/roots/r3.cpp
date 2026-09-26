#include <cstdio>
#include "akg_fixed.h"
static void show(const char* n, physics::QuarticCoeffs c) {
  auto R = physics::findRadialRoots(c);
  std::printf("%-34s nReal=%d:", n, R.nReal);
  for (auto z : R.roots) std::printf(" (%.6f,%.2e)", z.real(), z.imag());
  std::puts("");
}
int main() {
  physics::QuarticCoeffs c;
  c.c2 = -5; c.c1 = 0; c.c0 = 4; show("(r^2-1)(r^2-4) roots +-1,+-2", c);
  // (r-1)(r-2)(r-3)(r+6): sum=0 -> depressed. expand
  // (r^2-3r+2)(r^2+3r-18) = r^4 -27r^2... compute generically
  double r1=1,r2=2,r3=3,r4=-6;
  c.c2 = r1*r2+r1*r3+r1*r4+r2*r3+r2*r4+r3*r4; c.c1 = -(r1*r2*r3+r1*r2*r4+r1*r3*r4+r2*r3*r4); c.c0 = r1*r2*r3*r4;
  show("roots 1,2,3,-6", c);
}

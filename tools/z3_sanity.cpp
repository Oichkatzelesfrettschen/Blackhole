#include <z3++.h>

#include <iostream>

int main() {
  z3::context ctx;
  z3::solver solver(ctx);

  z3::expr x = ctx.int_const("x");
  z3::expr y = ctx.int_const("y");

  solver.add(x > 0);
  solver.add(y > 0);
  solver.add(x * x + y * y == 25);

  if (solver.check() != z3::sat) {
    std::cerr << "Z3 sanity check failed: unsat\n";
    return 1;
  }

  z3::model model = solver.get_model();
  std::cout << "Z3 sanity check passed: " << model << "\n";
  return 0;
}

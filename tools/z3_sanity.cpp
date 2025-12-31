#include <z3++.h>

#include <z3++.h>
#include <iostream>

int main() {
  z3::context ctx;
  {
    z3::solver solver(ctx);
    z3::expr x = ctx.int_const("x");
    z3::expr y = ctx.int_const("y");
    solver.add(x > 0);
    solver.add(y > 0);
    solver.add(x * x + y * y == 25);
    if (solver.check() != z3::sat) {
      std::cerr << "Z3 sanity check failed: integer circle unsat\n";
      return 1;
    }
    z3::model model = solver.get_model();
    std::cout << "Z3 sanity check passed: " << model << "\n";
  }

  {
    z3::solver solver(ctx);
    z3::expr mass = ctx.real_const("M");
    z3::expr radius = ctx.real_const("r");
    z3::expr r_s = 2 * mass;
    z3::expr redshift = 1 - r_s / radius;
    solver.add(mass > 0);
    solver.add(radius > r_s);
    solver.add(redshift <= 0);
    if (solver.check() != z3::unsat) {
      std::cerr << "Z3 sanity check failed: redshift constraint is satisfiable\n";
      return 1;
    }
    std::cout << "Z3 redshift constraint passed (unsat)\n";
  }

  return 0;
}

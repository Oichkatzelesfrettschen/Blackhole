#include "physics/math_types.h"
#include "physics/math_interop.h"
#include <glm/glm.hpp>

#if defined(BLACKHOLE_HAS_EIGEN) && BLACKHOLE_HAS_EIGEN
#include <Eigen/Core>
#endif

int main() {
  // Basic construction and data access should compile in either backend
  math::Vec3 v(1.0f, 2.0f, 3.0f);
  (void)math::dataPtr(v);

  glm::vec3 gv(1.0f, 2.0f, 3.0f);
#if defined(BLACKHOLE_HAS_EIGEN) && BLACKHOLE_HAS_EIGEN
  auto ev = math::toEigen(gv);
  (void)math::toGlm(ev);
#else
  (void)gv;
#endif
  return 0;
}

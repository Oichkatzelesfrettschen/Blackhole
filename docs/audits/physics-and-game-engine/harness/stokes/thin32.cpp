// FP32 emulation of the GLSL stokesStep I-channel emission factor (1-E)/A above the tauL<1e-4 guard,
// against a double expm1 reference; plus a 4-term series replacement.
#include <cmath>
#include <cstdio>
#include <initializer_list>
int main() {
  for (double t : {1.01e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2}) {
    double worst = 0, worstS = 0;
    for (int k = 0; k < 1000; ++k) {
      const float tau = float(t * (1.0 + 0.001 * k));
      const float A = 1.0f, L = tau;  // A = 1 so the factor equals (1-E)
      const float E = std::exp(-tau);
      const float glsl = (1.0f - E) / A;
      const float x = tau;
      const float series = L * (1.0f - x * (0.5f - x * (1.0f / 6.0f - x * (1.0f / 24.0f))));
      const double ref = -std::expm1(-double(tau));
      worst = std::fmax(worst, std::fabs(glsl - ref) / ref);
      worstS = std::fmax(worstS, std::fabs(series - ref) / ref);
    }
    std::printf("tauL~%-7g FP32 (1-E)/A max rel err %.2e | FP32 4-term series %.2e\n", t, worst, worstS);
  }
}

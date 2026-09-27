# Special Functions

The physics headers evaluate the modified Bessel function K_nu, the
synchrotron functions F and G, and Jacobi elliptic functions without Boost.
This page records what Boost computed, the in-house replacement, the
measurements that fixed its parameters, and the literature it was checked
against.

## Consumers

| Quantity | Header and symbol | Orders or parameter |
|---|---|---|
| F(x) = x int_x^inf K_{5/3} | `src/physics/synchrotron.h` `synchrotronF` | tail of K_{5/3} |
| G(x) = x K_{2/3}(x) | `src/physics/synchrotron.h` `synchrotronG`, GPU LUT via `synchrotronGGenerateLut` | K_{2/3} |
| Thermal j_nu partition factor | `src/physics/rte_integrator.h` `synchrotronThermalEmissivity` | K_2(1/Theta_e) |
| Faraday rotation and conversion | `src/physics/stokes_transport.h` `faradayRotationCoeffRelativistic`, `faradayConversionCoeff` | K_0/K_2, K_1/K_2 at 1/Theta_e |
| Analytic Kerr radial motion | `src/physics/analytic_kerr_geodesic.h` | Jacobi sn, cn at parameter m |

Shaders and CUDA kernels evaluate no Bessel function at run time. The GPU
reads G from the CPU-built LUT, so the double-precision CPU kernel is the
single implementation behind both paths.

## What Boost computed

Read from the headers of Boost 1.90.0 (Conan) and 1.92.0 (host). The files
below are byte-identical between the two versions.

- `cyl_bessel_k` (`special_functions/bessel.hpp`, `detail/bessel_ik.hpp`):
  integer orders dispatch to `bessel_kn`. Other orders split into
  nu = n + u with |u| <= 1/2, compute K_u and K_{u+1} by Temme's series for
  x <= 2 or Steed's continued fraction CF2 for x > 2, then recur upward in
  order. A large-x asymptotic branch applies only when |4 nu^2 - 25| / (8x)
  passes a fourth-root-epsilon test. Every loop stops on an
  epsilon-relative term test; the headers state no global error bound.
  Unscaled K underflows to zero near x = 745, so e^x K_nu cannot be rebuilt
  from it at large x.
- `jacobi_elliptic` (`special_functions/jacobi_elliptic.hpp`): arithmetic-
  geometric mean descent followed by an `asin` back-substitution, with
  special cases for k = 0, k = 1, and small k. Its near-one asymptotic is
  disabled in the source for insufficient precision.
- `ellint_1` and `ellint_rf`: Carlson R_F duplication with a seventh-order
  Taylor finish; complete K uses fitted polynomial bins up to m = 0.9 and
  R_F above it. The in-house `elliptic_integrals.h` already carries the
  Carlson forms.

Measured against mpmath on the reference grid below, Boost K stays within
7.3e-16 relative error through x = 700 in both versions.

## The in-house kernel

`src/physics/bessel_k.h` evaluates the exponentially scaled function and the
scaled tail integral from DLMF 10.32.9:

    e^x K_nu(x)              = int_0^inf e^{-x (cosh t - 1)} cosh(nu t) dt
    e^x int_x^inf K_nu(s) ds = int_0^inf e^{-x (cosh t - 1)} cosh(nu t) / cosh(t) dt

The integrand is even and analytic in a strip, so the trapezoid rule
converges exponentially in 1/h. The kernel integrates over [0, T(x)] with a
fixed N = 128 intervals, h = T / N, and cosh(t) - 1 written as 2
sinh(t/2)^2. T(x) solves x (cosh T - 1) - nu_max T = L with L = 40 (about
ln(1 / 2^-53) plus margin) by four fixed-point steps from acosh(1 + L / x),
with acosh(1 + y) evaluated as log1p(y + sqrt(y (2 + y))) so the range stays
positive where 1 + L / x rounds to 1 (x above 3.6e17). At large x, T shrinks
like sqrt(2L / x), so h tracks the integrand's width with no regime switch;
at small x, T grows like ln(2L / x).

One pass shares the factor e^{-x (cosh t - 1)} across several orders, so
K_0, K_1, and K_2 come from one loop and their ratios cancel the scale
exactly.

Measured in float64 with the same algorithm, maximum relative error over
orders {0, 1, 2, 1/3, 2/3, 5/3}:

| N | x in [1e-4, 1e5] (474-row table) | x in [1e-10, 1e10] |
|---:|---:|---:|
| 64 | 4.4e-16 | 1.9e-8 |
| 96 | -- | 8.1e-13 |
| 128 | 5.6e-16 | 5.6e-16 |

A fixed-step grid without the x-dependent truncation needs 577 nodes to
reach 8.8e-16 on [1e-4, 1e3] and loses accuracy past its largest x, because
the integrand narrows like 1/sqrt(x).

FP32 is not a target. On the host, a float32 trapezoid reached 8e-8 only
against references taken at the float32-rounded order; against the exact
orders 1/3, 2/3, and 5/3 it missed 1e-7 at small x, because rounding the
order alone moves e^x K_{5/3}(1e-4) by 4e-7. GPU consumers read
double-built LUTs.

## Reference table

`scripts/gen_bessel_k_reference.py` writes `tests/bessel_k_reference.inc`:
474 rows of {nu, x, e^x K_nu(x), e^x int_x^inf K_nu} at 50 digits, each
recomputed at 70 digits and required to agree to 1e-30. Each row is the
exact function at the binary64 order and argument the C++ test passes, so
nu is the double nearest 1/3, 2/3, or 5/3. The grid holds eight points per
decade from 1e-4 to 1e5 plus the LUT ends (0.001, 30) and one-sided samples
around x = 0.01 and x = 10. The tail integral is truncated where the
integrand bound falls below 10^-(dps + 10); that truncation reproduces
mpmath's `besselk` to 1e-71.

## Removed approximations

- F and G switched at x = 0.01 and x = 10 between leading asymptotes and a
  fitted middle. The Boost-free fitted G exceeded F on [1, 10], violating
  the polarization bound G <= F, and the F fit dropped about fifteenfold
  across x = 10.
- K_2(1/Theta_e) fell back to 2 Theta_e^2, a limit its own comment limits to
  Theta_e > 3, for every temperature.
- Faraday conversion switched at Theta_e = 0.5 between 1 and 0.5/Theta_e^2,
  a jump from 1 to 2 at the boundary.
- The Boost-path Faraday factors were wrong as well. Rotation used
  (K_0 + K_1) / (2 Theta_e^2 K_2), which grows as 1/Theta_e^2 in the cold
  limit instead of tending to 1; conversion used K_1 / (Theta_e K_2) -
  1 / (2 Theta_e^2), which the recurrence K_2 = K_0 + 2 K_1 / z makes negative
  at every temperature, so the clamp returned 0. `stokes_transport.h` now
  follows Dexter 2016 Eqs. B4-B5 in the high-frequency limit: rho_V carries
  K_0/K_2 on the cold-plasma n e^3 B_par / (pi m^2 c^2 nu^2), and rho_Q is
  n e^4 B_perp^2 / (4 pi^2 m^3 c^3 nu^3) times K_1/K_2 + 6 Theta_e. The cold
  rotation prefactor was low by 2 c^2; the test pins it to the standard
  rotation measure, 0.812 rad/m^2 for 1 cm^-3, 1 microgauss, and 1 pc.
- The thermal emissivity divided by K_2(1/Theta_e) after it underflowed,
  returning NaN for a cold plasma; it now folds e^{1/Theta_e} into the
  spectral exponential and returns the 0 limit.

## Literature

Titles verified against the arXiv records. None of these fits is used; they
bound what a closed-form approximation achieves.

- arXiv:2108.11560, "Fast parallel calculation of modified Bessel function
  of the second kind and its derivatives": integral representation with
  input-dependent integration bounds and a fixed number of divisions, the
  approach `bessel_k.h` follows.
- arXiv:2502.00356, "GPU-Accelerated Modified Bessel Function of the Second
  Kind for Gaussian Processes": Temme series for small x and a binned
  integral above it.
- arXiv:2409.08729, "Accurate Computation of the Logarithm of Modified
  Bessel Functions on GPUs": asymptotic forms with a log-stabilized integral
  fallback.
- arXiv:1006.1045 (Aharonian, Kelner, Prosekin), arXiv:1301.6908
  ("Analytical Fits to the Synchrotron Functions"), and arXiv:2602.15943
  ("New formula for Asymptotic behavior of the Synchrotron function"):
  closed-form F and G fits with reported errors of 0.035% to 0.26%, far
  above the kernel's.
- arXiv:1602.08749 (Pandya et al.), arXiv:1602.03184 (Dexter, grtrans), and
  arXiv:2108.10359 ("Updated Transfer Coefficients for Magnetized Plasmas"):
  thermal emissivity, absorptivity, and rotativity fits whose rho_Q and
  rho_V carry the K_1/K_2 and K_0/K_2 ratios.
- arXiv:2505.17159 ("Simple and accurate complete elliptic integrals for the
  full range of modulus") and arXiv:1803.05017 ("On Computing Jacobi's
  Elliptic Function sn"): AGM formulations of K, E, and sn.

#!/usr/bin/env python3
"""Reference constants for the Kerr-Newman, Kerr-de Sitter, and Kerr lapse tests.

Each value comes from an mpmath evaluation at 60 significant digits that is
independent of the C++ closed forms under test:

- Kerr-Newman metric components are expanded from the Carter form
  -(Delta/Sigma)(dt - a sin^2 dphi)^2 + (sin^2/Sigma)((r^2+a^2) dphi - a dt)^2
  + (Sigma/Delta) dr^2 + Sigma dtheta^2.
- The Kerr-Newman ISCO is the root of dE/dr = 0, where E(r) is the energy per
  unit mass of an equatorial circular geodesic of that metric. The script
  asserts that the closed-form marginal-stability function in
  src/physics/verified/kerr_newman.hpp vanishes at every root on a grid of
  signed spins and charges up to near extremality.

The tests in tests/kerr_newman_test.cpp embed the printed constants.

Usage: PYTHON=${PYTHON:-python3}; "$PYTHON" scripts/gen_kn_kds_reference.py
"""

import mpmath as mp

Real = mp.mpf

mp.mp.dps = 60


def kn_equatorial(r: Real, m: Real, a: Real, q: Real) -> tuple[tuple[Real, Real], ...]:
    """Equatorial (theta = pi/2) Carter-form components g_tt, g_tphi, g_phiphi
    and their exact r-derivatives."""
    delta = r * r - 2 * m * r + a * a + q * q
    d_delta = 2 * r - 2 * m
    rho2 = r * r
    d_rho2 = 2 * r
    num_tt = -delta + a * a
    num_tp = a * (delta - (r * r + a * a))
    num_pp = (r * r + a * a) ** 2 - delta * a * a
    d_num_tt = -d_delta
    d_num_tp = a * (d_delta - 2 * r)
    d_num_pp = 4 * r * (r * r + a * a) - d_delta * a * a

    def quotient(num: Real, d_num: Real) -> tuple[Real, Real]:
        return num / rho2, (d_num * rho2 - num * d_rho2) / rho2**2

    return quotient(num_tt, d_num_tt), quotient(num_tp, d_num_tp), quotient(num_pp, d_num_pp)


def circular_orbit_energy(r: Real, m: Real, a: Real, q: Real) -> Real:
    """Energy per unit mass of the equatorial circular geodesic with angular
    momentum along +z (signed a)."""
    (gtt, dgtt), (gtp, dgtp), (gpp, dgpp) = kn_equatorial(r, m, a, q)
    # Geodesic circularity: dgtt + 2 dgtp Omega + dgpp Omega^2 = 0.
    disc = mp.sqrt((2 * dgtp) ** 2 - 4 * dgpp * dgtt)
    omega = max((-2 * dgtp + disc) / (2 * dgpp), (-2 * dgtp - disc) / (2 * dgpp))
    u_t = 1 / mp.sqrt(-(gtt + 2 * gtp * omega + gpp * omega * omega))
    return -(gtt + gtp * omega) * u_t


def marginal_stability(r: Real, m: Real, a: Real, q: Real) -> Real:
    """Closed form used by verified::knIscoMarginalStability."""
    return (
        r * (6 * m * r - r * r - 9 * q * q + 3 * a * a)
        + 4 * q * q * (q * q - a * a) / m
        - 8 * a * mp.sqrt(m * r - q * q) ** 3 / m
    )


def outermost_marginal_root(m: Real, a: Real, q: Real) -> Real:
    """Outermost zero of the closed form, by an inward scan from 10 M."""
    floor = max(m + mp.sqrt(m * m - a * a - q * q), q * q / m)
    r_outer = 10 * m
    step = m / 200
    while r_outer - step > floor:
        if marginal_stability(r_outer - step, m, a, q) >= 0:
            return mp.findroot(
                lambda r: marginal_stability(r, m, a, q),
                (r_outer - step, r_outer),
                solver="anderson",
                verify=False,
            )
        r_outer -= step
    raise ValueError(f"no marginal-stability root for a={a}, q={q}")


def kn_isco(m: Real, a: Real, q: Real) -> Real:
    """ISCO from dE/dr = 0, polished from the closed-form bracket."""
    guess = outermost_marginal_root(m, a, q)
    root = mp.findroot(lambda r: mp.diff(lambda x: circular_orbit_energy(x, m, a, q), r), guess)
    assert abs(marginal_stability(root, m, a, q)) < mp.mpf(10) ** -30, (a, q)
    assert abs(root - guess) < mp.mpf(10) ** -20, (a, q, root, guess)
    return root


def kn_frame_dragging(r: Real, theta: Real, m: Real, a: Real, q: Real) -> Real:
    sigma = r * r + a * a * mp.cos(theta) ** 2
    delta = r * r - 2 * m * r + a * a + q * q
    sin2 = mp.sin(theta) ** 2
    g_tp = a * sin2 * (delta - (r * r + a * a)) / sigma
    g_pp = sin2 * ((r * r + a * a) ** 2 - delta * a * a * sin2) / sigma
    return -g_tp / g_pp


def rn_cubic_root(m: Real, q: Real) -> Real:
    return mp.findroot(lambda r: r**3 - 6 * m * r * r + 9 * q * q * r - 4 * q**4 / m, 5 * m)


def fmt(value: Real) -> str:
    return mp.nstr(value, 17)


def kerr_newman_section() -> None:
    one = mp.mpf(1)
    print("# Kerr-Newman (M = 1)")
    for q in ("0.5", "0.9"):
        q = mp.mpf(q)
        isco = kn_isco(one, mp.mpf(0), q)
        cubic = rn_cubic_root(one, q)
        assert abs(isco - cubic) < mp.mpf(10) ** -25
        print(f"isco a=0 Q={mp.nstr(q, 3)}: {fmt(isco)}  (RN cubic {fmt(cubic)})")
    for a, q in (("0.5", "0.5"), ("0.9", "0.3")):
        a, q = mp.mpf(a), mp.mpf(q)
        print(
            f"isco a={mp.nstr(a, 3)} Q={mp.nstr(q, 3)}: prograde {fmt(kn_isco(one, a, q))}"
            f"  retrograde {fmt(kn_isco(one, -a, q))}"
        )
    omega = kn_frame_dragging(mp.mpf(3), mp.pi / 2, one, mp.mpf("0.5"), mp.mpf("0.5"))
    print(f"omega r=3 theta=pi/2 a=Q=0.5: {fmt(omega)}")
    # Grid check of the closed form, including a < 0, near-extremal charge,
    # and M != 1 so that a dimensionally inconsistent term cannot hide.
    count = 0
    for m in (one, mp.mpf("2.5")):
        for a_star in ("-0.99", "-0.6", "-0.2", "0", "0.3", "0.7", "0.95", "0.998"):
            a = mp.mpf(a_star) * m
            for fraction in ("0", "0.3", "0.7", "0.99"):
                q = mp.mpf(fraction) * mp.sqrt(m * m - a * a)
                kn_isco(m, a, q)
                count += 1
    print(f"closed-form marginal stability matches dE/dr = 0 on {count} (a, Q) points")


def main() -> None:
    kerr_newman_section()


if __name__ == "__main__":
    main()

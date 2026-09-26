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

- Kerr clock rates at the equator: the ZAMO lapse sqrt(Sigma Delta / A), the
  static-observer rate sqrt(-g_tt), and 1/u^t of circular geodesics with u^t
  from the metric's circularity condition, independent of the
  Bardeen-Press-Teukolsky closed form under test.
- Kerr-de Sitter horizons are the positive real roots of the Carter quartic
  Delta_r = (r^2 + a^2)(1 - Lambda r^2 / 3) - 2 M r, from mpmath.polyroots on
  its coefficients rather than the bracketing solver under test.
- Kerr-de Sitter metric components at one point come from the Carter line
  element assembled from its covectors, including the Xi normalization that
  the Ricci check cannot see.

The tests in tests/kerr_newman_test.cpp, tests/kerr_de_sitter_test.cpp, and
tests/kerr_clock_rates_test.cpp embed the printed constants.

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


def circular_orbit(r: Real, m: Real, a: Real, q: Real) -> tuple[Real, Real]:
    """(E, u^t) of the equatorial circular geodesic with angular momentum
    along +z (signed a)."""
    (gtt, dgtt), (gtp, dgtp), (gpp, dgpp) = kn_equatorial(r, m, a, q)
    # Geodesic circularity: dgtt + 2 dgtp Omega + dgpp Omega^2 = 0.
    disc = mp.sqrt((2 * dgtp) ** 2 - 4 * dgpp * dgtt)
    omega = max((-2 * dgtp + disc) / (2 * dgpp), (-2 * dgtp - disc) / (2 * dgpp))
    u_t = 1 / mp.sqrt(-(gtt + 2 * gtp * omega + gpp * omega * omega))
    return -(gtt + gtp * omega) * u_t, u_t


def circular_orbit_norm(r: Real, m: Real, a: Real, q: Real) -> Real:
    """-(g_tt + 2 g_tphi Omega + g_phiphi Omega^2) for the circular geodesic
    with angular momentum along +z; zero where the orbit becomes null."""
    (gtt, dgtt), (gtp, dgtp), (gpp, dgpp) = kn_equatorial(r, m, a, q)
    disc = mp.sqrt((2 * dgtp) ** 2 - 4 * dgpp * dgtt)
    omega = max((-2 * dgtp + disc) / (2 * dgpp), (-2 * dgtp - disc) / (2 * dgpp))
    return -(gtt + 2 * gtp * omega + gpp * omega * omega)


def photon_orbit_function(r: Real, m: Real, a: Real, q: Real) -> Real:
    """Closed form used by verified::knPhotonOrbitFunction."""
    return r * r - 3 * m * r + 2 * q * q + 2 * a * mp.sqrt(m * r - q * q)


def kn_photon_orbit(m: Real, a: Real, q: Real) -> Real:
    """Photon orbit from the null limit of circular geodesics, checked against
    the closed form."""
    r_outer = 5 * m
    step = m / 200
    while photon_orbit_function(r_outer - step, m, a, q) > 0:
        r_outer -= step
    guess = mp.findroot(
        lambda r: photon_orbit_function(r, m, a, q),
        (r_outer - step, r_outer),
        solver="anderson",
        verify=False,
    )
    root = mp.findroot(lambda r: circular_orbit_norm(r, m, a, q), guess)
    assert abs(root - guess) < mp.mpf(10) ** -20, (a, q, root, guess)
    return root


def circular_orbit_energy(r: Real, m: Real, a: Real, q: Real) -> Real:
    return circular_orbit(r, m, a, q)[0]


def marginal_stability(r: Real, m: Real, a: Real, q: Real) -> Real:
    """Closed form used by verified::knIscoMarginalStability."""
    return (
        r * (6 * m * r - r * r - 9 * q * q + 3 * a * a)
        + 4 * q * q * (q * q - a * a) / m
        - 8 * a * mp.sqrt(m * r - q * q) ** 3 / m
    )


def outermost_marginal_root(m: Real, a: Real, q: Real) -> Real:
    """Outermost zero of the closed form, by an inward scan from 10 M."""
    # max(0, .) keeps an extremal input whose decimal a, Q round the
    # discriminant to -1e-60 on the real axis.
    floor = max(m + mp.sqrt(max(0, m * m - a * a - q * q)), q * q / m)
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
    for a, q in (("0", "0"), ("0", "0.5"), ("0", "1"), ("0.5", "0.5"), ("0.9", "0.3")):
        a, q = mp.mpf(a), mp.mpf(q)
        print(
            f"photon orbit a={mp.nstr(a, 3)} Q={mp.nstr(q, 3)}: prograde "
            f"{fmt(kn_photon_orbit(one, a, q))}  retrograde {fmt(kn_photon_orbit(one, -a, q))}"
        )
    # Extremal a^2 + Q^2 = M^2: r_+ = r_- = M. The prograde photon-orbit function
    # stays positive for every r > r_+, so that orbit sits at the floor r_+.
    a, q = mp.mpf("0.6"), mp.mpf("0.8")
    assert photon_orbit_function(one + mp.mpf(10) ** -12, one, a, q) > 0
    print(
        f"extremal a=0.6 Q=0.8: isco prograde {fmt(kn_isco(one, a, q))}"
        f"  retrograde {fmt(kn_isco(one, -a, q))}"
        f"  photon retrograde {fmt(kn_photon_orbit(one, -a, q))}  photon prograde r_+ = 1"
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


def kds_delta(r: Real, m: Real, a: Real, lam: Real) -> Real:
    return (r * r + a * a) * (1 - lam * r * r / 3) - 2 * m * r


def kds_horizons(m: Real, a: Real, lam: Real) -> list[Real]:
    """Positive real roots of Delta_r, ascending, each polished by findroot.

    At a = 0 Delta_r = r (-(L/3) r^3 + r - 2 M) and the factor r is removed so
    that the root r = 0 cannot surface as a spurious positive root. The
    imaginary-part filter is relative to |z| because the roots span from
    ~1 M to ~sqrt(3 / Lambda).
    """
    # Delta_r = -(L/3) r^4 + (1 - L a^2 / 3) r^2 - 2 M r + a^2
    coefficients = [-lam / 3, 0, 1 - lam * a * a / 3, -2 * m, a * a]
    if a == 0:
        coefficients = coefficients[:-1]
    roots = mp.polyroots(coefficients, maxsteps=2000, extraprec=2000)
    real = sorted(
        mp.re(z) for z in roots if abs(mp.im(z)) < mp.mpf(10) ** -40 * abs(z) and mp.re(z) > 0
    )
    expected = 2 if a == 0 else 3
    assert len(real) == expected, (a, lam, roots)
    # Delta_r / (r^2 + a^2) is O(1) at every root, so findroot's absolute
    # tolerance is meaningful from r ~ M to r ~ sqrt(3 / Lambda).
    # The secant starts from two points 1e-45 apart around each polyroots root,
    # which keeps it on that root when r_- and r_+ nearly merge (a -> M).
    step = mp.mpf(10) ** -45
    polished = [
        mp.findroot(
            lambda r: kds_delta(r, m, a, lam) / (r * r + a * a), (x * (1 - step), x * (1 + step))
        )
        for x in real
    ]
    for x, y in zip(real, polished, strict=True):
        assert abs(x - y) < mp.mpf(10) ** -40 * y, (a, lam, x, y)
    return polished


def kds_carter_metric(r: Real, theta: Real, m: Real, a: Real, lam: Real) -> list[list[Real]]:
    """Carter-form line element assembled from its covectors.

    ds^2 = -(Delta_r / (Xi^2 Sigma)) (dt - a sin^2 dphi)^2
         + (Delta_theta sin^2 / (Xi^2 Sigma)) (a dt - (r^2 + a^2) dphi)^2
         + (Sigma / Delta_r) dr^2 + (Sigma / Delta_theta) dtheta^2
    (Carter 1973, Les Houches lectures "Black hole equilibrium states";
    Griffiths & Podolsky 2009, Kerr-de Sitter in Boyer-Lindquist-type
    coordinates). Coordinates (t, r, theta, phi).
    """
    sigma = r * r + a * a * mp.cos(theta) ** 2
    delta_r = kds_delta(r, m, a, lam)
    delta_theta = 1 + lam * a * a * mp.cos(theta) ** 2 / 3
    xi = 1 + lam * a * a / 3
    sin2 = mp.sin(theta) ** 2
    w_time = [1, 0, 0, -a * sin2]
    w_rot = [a, 0, 0, -(r * r + a * a)]
    c_time = -delta_r / (xi * xi * sigma)
    c_rot = delta_theta * sin2 / (xi * xi * sigma)
    g = [
        [c_time * w_time[i] * w_time[j] + c_rot * w_rot[i] * w_rot[j] for j in range(4)]
        for i in range(4)
    ]
    g[1][1] += sigma / delta_r
    g[2][2] += sigma / delta_theta
    return g


def kerr_de_sitter_section() -> None:
    one = mp.mpf(1)
    print("# Kerr-de Sitter (M = 1), positive roots of Delta_r ascending")
    cases = [("0", "1e-2"), ("0", "1e-4"), ("0.9", "1e-2"), ("0.9", "0.1"), ("0.5", "1e-10")]
    # Lambda M^2 from M87* (~1e-26) to a stellar-mass hole (~1e-44).
    cases += [(a, lam) for lam in ("1e-26", "1e-34", "1e-44") for a in ("0", "0.5", "0.999")]
    for a, lam in cases:
        roots = kds_horizons(one, mp.mpf(a), mp.mpf(lam))
        print(f"a={a} Lambda={lam}: " + ", ".join(fmt(x) for x in roots))
    lam = mp.mpf("1e-2")
    r = mp.mpf(10)
    g_tt = -(1 - 2 / r - lam * r * r / 3)
    print(f"SdS g_tt r=10 Lambda=1e-2: {fmt(g_tt)}  g_rr: {fmt(-1 / g_tt)}")
    g = kds_carter_metric(mp.mpf(3), mp.pi / 3, one, mp.mpf("0.9"), mp.mpf("1e-2"))
    print(
        "Carter metric r=3 theta=pi/3 a=0.9 Lambda=1e-2: "
        f"g_tt {fmt(g[0][0])}  g_tphi {fmt(g[0][3])}  g_phiphi {fmt(g[3][3])}"
    )


def kerr_clock_section() -> None:
    one = mp.mpf(1)
    print("# Kerr clock rates dtau/dt at the equator (M = 1)")
    for a, r in (("0.9", "6"), ("0.9", "3"), ("0.9", "1.8"), ("0.9", "1.6"), ("0", "6")):
        a, r = mp.mpf(a), mp.mpf(r)
        delta = r * r - 2 * r + a * a
        big_a = (r * r + a * a) ** 2 - a * a * delta
        zamo = mp.sqrt(r * r * delta / big_a)
        minus_gtt = 1 - 2 / r
        static = mp.sqrt(minus_gtt) if minus_gtt > 0 else None
        line = f"a={mp.nstr(a, 3)} r={mp.nstr(r, 3)}: zamo {fmt(zamo)}"
        line += f"  static {fmt(static)}" if static is not None else "  static none (ergoregion)"
        for label, sign in (("prograde", 1), ("retrograde", -1)):
            photon = 2 * (1 + mp.cos(mp.mpf(2) / 3 * mp.acos(-sign * a)))
            if r > photon:
                u_t = circular_orbit(r, one, sign * a, mp.mpf(0))[1]
                line += f"  {label} {fmt(1 / u_t)}"
            else:
                line += f"  {label} none (r <= photon orbit {mp.nstr(photon, 6)})"
        print(line)


def main() -> None:
    kerr_newman_section()
    kerr_de_sitter_section()
    kerr_clock_section()


if __name__ == "__main__":
    main()

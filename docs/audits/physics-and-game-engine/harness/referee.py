"""Literature referee for Kerr / Kerr-Newman / Kerr-de Sitter equatorial quantities.

Metrics are written from textbook forms, never from either repository:
  Kerr, Kerr-Newman: Misner-Thorne-Wheeler 33.2 / Carter 1968 (g_tphi = -a sin^2 (2Mr-Q^2)/Sigma).
  Kerr-de Sitter: Carter 1968, Delta_r = (r^2+a^2)(1-L r^2/3) - 2Mr,
                  Delta_th = 1 + L a^2 cos^2/3, Xi = 1 + L a^2/3.
Circular orbits from the metric (Omega from dg/dr), ISCO = dE/dr = 0,
photon orbit = u^t normalization diverges, Page-Thorne flux by quadrature.
"""
import mpmath as mp

mp.mp.dps = 30
M = mp.mpf(1)


def kn_eq(r, a, Q):
    # equatorial theta = pi/2, Sigma = r^2
    S = r * r
    D = r * r - 2 * M * r + a * a + Q * Q
    gtt = -(1 - (2 * M * r - Q * Q) / S)
    gtp = -a * (2 * M * r - Q * Q) / S
    A = (r * r + a * a) ** 2 - a * a * D
    gpp = A / S
    return gtt, gtp, gpp


def kds_eq(r, a, L):
    S = r * r
    Dr = (r * r + a * a) * (1 - L * r * r / 3) - 2 * M * r
    Dth = 1  # cos theta = 0
    Xi = 1 + L * a * a / 3
    # ds^2 = -(Dr/(S Xi^2))(dt - a dphi)^2 + (Dth/(S Xi^2))(a dt - (r^2+a^2) dphi)^2 at equator
    gtt = (-Dr + Dth * a * a) / (S * Xi ** 2)
    gtp = (Dr * a - Dth * a * (r * r + a * a)) / (S * Xi ** 2)
    gpp = (-Dr * a * a + Dth * (r * r + a * a) ** 2) / (S * Xi ** 2)
    return gtt, gtp, gpp


def omega(metric, r, prograde=True):
    d = [mp.diff(lambda x: metric(x)[i], r) for i in range(3)]
    gtt_r, gtp_r, gpp_r = d
    disc = mp.sqrt(gtp_r ** 2 - gtt_r * gpp_r)
    s = 1 if prograde else -1
    return (-gtp_r + s * disc) / gpp_r


def orbit(metric, r, prograde=True):
    gtt, gtp, gpp = metric(r)
    W = omega(metric, r, prograde)
    norm = -(gtt + 2 * gtp * W + gpp * W * W)
    ut = 1 / mp.sqrt(norm)
    E = -(gtt + gtp * W) * ut
    Lz = (gtp + gpp * W) * ut
    return W, E, Lz, ut, norm


def isco(metric, lo, hi, prograde=True):
    f = lambda r: mp.diff(lambda x: orbit(metric, x, prograde)[1], r)
    return bisect(f, lo, hi)


def photon_orbit(metric, lo, hi, prograde=True):
    f = lambda r: orbit_norm(metric, r, prograde)
    return bisect(f, lo, hi)


def bisect(f, lo, hi, n=70):
    flo = f(lo)
    for _ in range(n):
        mid = (lo + hi) / 2
        fm = f(mid)
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi = mid
    return (lo + hi) / 2


def orbit_norm(metric, r, prograde):
    gtt, gtp, gpp = metric(r)
    W = omega(metric, r, prograde)
    return -(gtt + 2 * gtp * W + gpp * W * W)


# ---------------------------------------------------------------- Kerr closed forms
def bpt_isco(a, pro=True):
    z1 = 1 + mp.cbrt(1 - a * a) * (mp.cbrt(1 + a) + mp.cbrt(1 - a))
    z2 = mp.sqrt(3 * a * a + z1 * z1)
    s = -1 if pro else 1
    return 3 + z2 + s * mp.sqrt((3 - z1) * (3 + z1 + 2 * z2))


def kerr_zamo_alpha(r, th, a):
    S = r * r + a * a * mp.cos(th) ** 2
    D = r * r - 2 * r + a * a
    A = (r * r + a * a) ** 2 - a * a * D * mp.sin(th) ** 2
    return mp.sqrt(S * D / A)


def kerr_static(r, th, a):
    S = r * r + a * a * mp.cos(th) ** 2
    v = 1 - 2 * r / S
    return mp.sqrt(v) if v > 0 else mp.nan


def blackhole_docstring_zamo(r, a):
    # kerr.h:340 "dtau/dt = sqrt(Delta Sigma) / (r^2 + a^2 + 2Ma^2/r)" at equator
    D = r * r - 2 * r + a * a
    return mp.sqrt(D * r * r) / (r * r + a * a + 2 * a * a / r)


# ---------------------------------------------------------------- Page-Thorne
def page_thorne_closed(x, a):
    """Page & Thorne 1974 closed form (Kerr, M=1), returns f such that
    F = (3 Mdot / (8 pi r^3)) * f ; f -> 1 at large r.  x = sqrt(r)."""
    x0 = mp.sqrt(bpt_isco(a, True))
    ac = mp.acos(a)
    x1 = 2 * mp.cos(ac / 3 - mp.pi / 3)
    x2 = 2 * mp.cos(ac / 3 + mp.pi / 3)
    x3 = -2 * mp.cos(ac / 3)
    br = (x - x0 - mp.mpf(3) / 2 * a * mp.log(x / x0)
          - 3 * (x1 - a) ** 2 / (x1 * (x1 - x2) * (x1 - x3)) * mp.log((x - x1) / (x0 - x1))
          - 3 * (x2 - a) ** 2 / (x2 * (x2 - x1) * (x2 - x3)) * mp.log((x - x2) / (x0 - x2))
          - 3 * (x3 - a) ** 2 / (x3 * (x3 - x1) * (x3 - x2)) * mp.log((x - x3) / (x0 - x3)))
    # F = 3 Mdot/(8 pi M^2) * 1/(x^4 (x^3 - 3x + 2a)) * br   and 3Mdot M/(8 pi r^3) = 3Mdot/(8pi x^6)
    return x ** 6 / (x ** 4 * (x ** 3 - 3 * x + 2 * a)) * br


def page_thorne_quad(r, a):
    """Independent: F = -Omega_r/(E - Omega L)^2 * int (E - Omega L) L_r dr / (4 pi sqrt(-g)),
    sqrt(-g) = r at the Kerr equator in (t, r, z, phi); normalized as page_thorne_closed."""
    met = lambda x: kn_eq(x, a, 0)
    rin = bpt_isco(a, True)
    Wf = lambda x: orbit(met, x)[0]
    Ef = lambda x: orbit(met, x)[1]
    Lf = lambda x: orbit(met, x)[2]
    integrand = lambda x: (Ef(x) - Wf(x) * Lf(x)) * mp.diff(Lf, x)
    I = mp.quad(integrand, [rin, r])
    F = -mp.diff(Wf, r) / (Ef(r) - Wf(r) * Lf(r)) ** 2 * I / (4 * mp.pi * r)
    return F / (3 / (8 * mp.pi * r ** 3))


if __name__ == "__main__":
    import json
    out = {}
    spins = [0, 0.5, 0.9, 0.998, -0.9]
    for a in spins:
        a = mp.mpf(a)
        met = lambda x, a=a: kn_eq(x, a, 0)
        row = {}
        rp = 1 + mp.sqrt(1 - a * a)
        row["r_plus"] = rp
        row["r_minus"] = 1 - mp.sqrt(1 - a * a)
        row["isco_pro_bpt"] = bpt_isco(a, True)
        row["isco_ret_bpt"] = bpt_isco(a, False)
        row["rph_pro"] = photon_orbit(met, rp + mp.mpf("1e-4"), mp.mpf("4.6"), True)
        row["rph_ret"] = photon_orbit(met, rp + mp.mpf("1e-4"), mp.mpf("4.6"), False)
        row["isco_pro_metric"] = isco(met, row["rph_pro"] + mp.mpf("1e-3"), mp.mpf(12), True)
        row["isco_ret_metric"] = isco(met, row["rph_ret"] + mp.mpf("1e-3"), mp.mpf(12), False)
        row["E_isco"] = orbit(met, row["isco_pro_metric"])[1]
        row["eta"] = 1 - row["E_isco"]
        # time dilation at r = 3, theta = pi/2 and r = 1.5 (inside ergosphere for a>0.7)
        for r in [mp.mpf(3), mp.mpf(6), mp.mpf("1.8")]:
            if r > rp:
                row[f"zamo_r{r}"] = kerr_zamo_alpha(r, mp.pi / 2, a)
                row[f"static_r{r}"] = kerr_static(r, mp.pi / 2, a)
                row[f"docz_r{r}"] = blackhole_docstring_zamo(r, a)
        # circular orbit 1/u^t at ISCO
        row["inv_ut_isco"] = 1 / orbit(met, row["isco_pro_metric"])[3]
        out[f"kerr a={float(a)}"] = row

    # Page-Thorne flux shape
    pt = {}
    for a in [0, 0.5, 0.9, 0.998]:
        a = mp.mpf(a)
        rin = bpt_isco(a)
        for k in [1.5, 2.0, 4.0]:
            r = rin * k
            c = page_thorne_closed(mp.sqrt(r), a)
            q = page_thorne_quad(r, a)
            newton = 1 - mp.sqrt(rin / r)
            bh_kerr = newton * (1 + mp.mpf("0.5") * a * mp.sqrt(1 / r)) if a != 0 else None
            x = mp.sqrt(r); xin = mp.sqrt(rin)
            bh_schw = (newton - (mp.mpf(3) / (2 * x * x)) * mp.log(x / xin)) - (3 * (x - xin)) / (x * x * xin)
            pt[f"a={float(a)} r={k}risco"] = dict(closed=c, quad=q, newtonian=newton,
                                                  bh_kerr_approx=bh_kerr, bh_schw_factor=bh_schw)
    out["page_thorne"] = pt

    # Kerr-Newman ISCO, a=0 anchored against RN cubic
    kn = {}
    for a, Q in [(0, 0.5), (0, 0.9), (0.5, 0.5), (0.9, 0.3)]:
        a = mp.mpf(a); Q = mp.mpf(Q)
        met = lambda x, a=a, Q=Q: kn_eq(x, a, Q)
        rp = 1 + mp.sqrt(1 - a * a - Q * Q)
        php = photon_orbit(met, rp + mp.mpf("1e-4"), mp.mpf("4.6"), True)
        phr = photon_orbit(met, rp + mp.mpf("1e-4"), mp.mpf("4.6"), False)
        ip = isco(met, php + mp.mpf("1e-3"), mp.mpf(12), True)
        ir = isco(met, phr + mp.mpf("1e-3"), mp.mpf(12), False)
        repo = bpt_isco(a, True) + Q * Q / 2
        # frame dragging at r=3
        gtt, gtp, gpp = met(mp.mpf(3))
        om_true = -gtp / gpp
        A = (9 + a * a) ** 2 - a * a * (9 - 6 + a * a + Q * Q)
        om_repo = 2 * 3 * a / A if a != 0 else mp.mpf(0)
        rn_cubic = None
        if a == 0:
            rn_cubic = mp.findroot(lambda r: r ** 3 - 6 * r * r + 9 * Q * Q * r - 4 * Q ** 4, 5.5)
        kn[f"a={float(a)} Q={float(Q)}"] = dict(r_plus=rp, isco_pro=ip, isco_ret=ir, repo_isco_pro=repo,
                                                repo_isco_ret=bpt_isco(a, False) + Q * Q / 2,
                                                rn_cubic=rn_cubic, omega_r3_true=om_true, omega_r3_repo=om_repo)
    out["kerr_newman"] = kn

    # Kerr-de Sitter horizons: roots of the Carter quartic vs repo approximations
    kds = {}
    for a in [0, 0.9]:
        for L in ["1e-4", "1e-2", "0.1"]:
            a_ = mp.mpf(a); L_ = mp.mpf(L)
            poly = [-L_ / 3, 0, 1 - L_ * a_ * a_ / 3, -2, a_ * a_]
            roots = sorted([mp.re(z) for z in mp.polyroots(poly, maxsteps=200, extraprec=200) if abs(mp.im(z)) < 1e-20])
            rk = 1 + mp.sqrt(1 - a_ * a_)
            rkm = 1 - mp.sqrt(1 - a_ * a_)
            kds[f"a={a} L={L}"] = dict(roots=roots, repo_event=rk + L_ * rk ** 3 / 3,
                                        repo_inner=rkm - L_ * rkm ** 3 / 3, repo_cosmo=mp.sqrt(3 / L_))
    out["kds"] = kds

    # KdS ISCO shift for small Lambda at a=0.9 (Carter metric)
    for L in ["1e-4", "1e-2"]:
        met = lambda x, L=mp.mpf(L): kds_eq(x, mp.mpf("0.9"), L)
        out["kds"][f"isco a=0.9 L={L}"] = isco(met, mp.mpf("1.8"), mp.mpf("4"), True)

    # Synchrotron F(x) and G(x)
    sy = {}
    for x in [0.01, 0.1, 0.5, 1.0, 3.0, 10.0]:
        x = mp.mpf(x)
        F = x * mp.quad(lambda t: mp.besselk(mp.mpf(5) / 3, t), [x, mp.inf])
        G = x * mp.besselk(mp.mpf(2) / 3, x)
        poly = mp.mpf("1.8084") * x ** (mp.mpf(1) / 3) * mp.exp(-x) * (1 + mp.mpf("0.884") * x ** (mp.mpf(2) / 3) + mp.mpf("0.471") * x ** (mp.mpf(4) / 3))
        gpoly = mp.mpf("1.3541") * x ** (mp.mpf(1) / 3) * mp.exp(-x) * (1 + mp.mpf("0.6") * x ** (mp.mpf(2) / 3))
        sy[f"x={float(x)}"] = dict(F=F, F_poly=poly, G=G, G_poly=gpoly)
    out["synchrotron"] = sy

    # Kerr disk orbital velocity in ZAMO frame (BPT 1972 eq 3.10) vs repo formula
    dv = {}
    for a, r in [(0, 6), (0.9, 3), (0.9, 2.5), (0.998, 1.5)]:
        a = mp.mpf(a); r = mp.mpf(r)
        v_bpt = (r * r - 2 * a * mp.sqrt(r) + a * a) / (mp.sqrt(r * r - 2 * r + a * a) * (r ** mp.mpf(1.5) + a))
        v_repo = mp.sqrt(1 / (r - 2 + a * mp.sqrt(1 / r)))
        dv[f"a={float(a)} r={float(r)}"] = dict(v_bpt=v_bpt, v_repo=v_repo)
    out["disk_velocity"] = dv

    # Photon-ring Lyapunov exponent (Johnson et al. 2020, Schwarzschild gamma = pi)
    def fmt(v):
        if isinstance(v, dict):
            return {k: fmt(w) for k, w in v.items()}
        if isinstance(v, list):
            return [fmt(w) for w in v]
        if v is None:
            return None
        return float(v)
    print(json.dumps(fmt(out), indent=1))

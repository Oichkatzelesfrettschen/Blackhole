"""Clock-rate, canon, tidal, and delay numbers for the game-layer audit (M = G = c = 1)."""
from mpmath import mp, mpf, sqrt, cbrt, acos, cos, log, pi, findroot, quad

mp.dps = 60
TARGET = mpf(7) * mpf("365.25") * 24  # 1 hour = 7 Julian years
MSUN_G = mpf("1.98847e33")
G = mpf("6.67430e-8")
C = mpf("2.99792458e10")
DAY = mpf(86400)


def rplus(a):
    return 1 + sqrt(1 - a * a)


def isco(a, pro=True):
    z1 = 1 + cbrt(1 - a * a) * (cbrt(1 + a) + cbrt(1 - a))
    z2 = sqrt(3 * a * a + z1 * z1)
    s = sqrt((3 - z1) * (3 + z1 + 2 * z2))
    return 3 + z2 - s if pro else 3 + z2 + s


def rph(a, pro=True):
    return 2 * (1 + cos(mpf(2) / 3 * acos(-a if pro else a)))


def rmb(a, pro=True):
    s = 1 if pro else -1
    return 2 - s * a + 2 * sqrt(1 - s * a)


def circ(r, a, pro=True):
    s = 1 if pro else -1
    x = 1 - 3 / r + 2 * s * a * r ** mpf(-1.5)
    if x <= 0:
        return None
    return sqrt(x) / (1 + s * a * r ** mpf(-1.5))


def zamo(r, a):
    d = r * r - 2 * r + a * a
    big_a = (r * r + a * a) ** 2 - a * a * d
    return sqrt(r * r * d / big_a)


def static(r):
    return sqrt(1 - 2 / r) if r > 2 else None


def energy_l(r, a):
    den = r ** mpf(0.75) * sqrt(r ** mpf(1.5) - 3 * sqrt(r) + 2 * a)
    e = (r ** mpf(1.5) - 2 * sqrt(r) + a) / den
    l = (r * r - 2 * a * sqrt(r) + a * a) / den
    return e, l


def tidal_stretch(r, a):
    """Marck (1983) radial eigenvalue magnitude for an equatorial circular orbit, units 1/M^2."""
    e, l = energy_l(r, a)
    k = (l - a * e) ** 2
    return (2 + 3 * k / (r * r)) / r ** 3


def fmt(x, n=6):
    return "n/a" if x is None else mp.nstr(x, n)


print("== Repo default scenario: a* = 0.9, bands 0.85/3/10/50 r_s, authority 200 r_s ==")
a = mpf("0.9")
print("r+", fmt(rplus(a)), "ergo 2", "rph_pro", fmt(rph(a)), "rmb_pro", fmt(rmb(a)),
      "isco_pro", fmt(isco(a)), "rph_ret", fmt(rph(a, False)), "isco_ret", fmt(isco(a, False)))
for r in [mpf("1.7"), mpf(6), mpf(20), mpf(100), mpf(400)]:
    zp = zamo(r, a)
    cp = circ(r, a, True)
    cr = circ(r, a, False)
    st = static(r)
    print(f"r={fmt(r,4)}M zamo={fmt(zp,6)} static={fmt(st,6)} circ_pro={fmt(cp,6)}"
          f" circ_ret={fmt(cr,6)} pro_stable={r > isco(a)} ret_stable={r > isco(a, False)}"
          f" ret_exists={r > rph(a, False)}")

print("\n== Schwarzschild field (BlackholeTimeField): static vs circular geodesic ==")
for r in [mpf(6), mpf(20), mpf(100)]:
    print(f"r={fmt(r,4)}M static={fmt(static(r),6)} circ={fmt(circ(r, mpf(0)),6)}")

print("\n== Canon: spin that puts 1 h = 7 yr (factor", fmt(TARGET, 7), ") at the prograde ISCO ==")


def dil_at_isco(logdelta):
    aa = 1 - mpf(10) ** logdelta
    return 1 / circ(isco(aa), aa) - TARGET


root = findroot(dil_at_isco, mpf(-14))
a_c = 1 - mpf(10) ** root
r_c = isco(a_c)
f_c = circ(r_c, a_c)
print("1-a =", fmt(1 - a_c, 6), " r_isco/M =", fmt(r_c, 12), " (r_isco-1)/M =", fmt(r_c - 1, 6))
print("dtau/dt =", fmt(f_c, 8), " zamo lapse there =", fmt(zamo(r_c, a_c), 8),
      " ratio circ/zamo =", fmt(f_c / zamo(r_c, a_c), 6))
e_c, l_c = energy_l(r_c, a_c)
print("E =", fmt(e_c, 8), " L =", fmt(l_c, 8))

for spin in [mpf("0.6"), mpf("0.9"), mpf("0.998"), mpf("0.9999"), 1 - mpf("1e-8"), 1 - mpf("1e-14")]:
    ri = isco(spin)
    fi = circ(ri, spin)
    print(f"a=1-{fmt(1-spin,3)} isco={fmt(ri,8)} circ dtau/dt={fmt(fi,6)} dilation={fmt(1/fi,6)}"
          f" zamo@isco={fmt(zamo(ri, spin),6)}")

print("\n== ZAMO-model radius where lapse = 1/", fmt(TARGET, 7), " (repo KerrTimeField) ==")
for spin in [mpf("0.6"), mpf("0.9"), mpf("0.998")]:
    rp = rplus(spin)
    g = lambda lx: zamo(rp + mpf(10) ** lx, spin) - 1 / TARGET
    lx = findroot(g, mpf(-8))
    print(f"a={fmt(spin,4)} r+={fmt(rp,8)} (r-r+)/M={fmt(mpf(10)**lx,4)} "
          f"circ orbit exists there: {circ(rp + mpf(10)**lx, spin) is not None}")

print("\n== Orbital period and tidal stretch at the canon ISCO, M = 1e8 Msun ==")
mass_g = mpf("1e8") * MSUN_G
m_cm = G * mass_g / C ** 2
m_s = m_cm / C
t_coord = 2 * pi * (r_c ** mpf(1.5) + a_c) * m_s
print("GM/c^3 =", fmt(m_s, 6), "s  coordinate period =", fmt(t_coord / 3600, 5), "h",
      " proper period =", fmt(t_coord * f_c, 5), "s")
lam = tidal_stretch(r_c, a_c)
grad = lam / m_cm ** 2 * C ** 2
rho_crit = grad / (4 * pi / 3 * G)
print("Marck stretch eigenvalue =", fmt(lam, 6), "/M^2 ;", "gradient =", fmt(grad, 5), "s^-2 ;",
      "rho_crit (self-gravity = tidal) =", fmt(rho_crit, 4), "g/cm^3 ;",
      "earth-radius stretch accel =", fmt(grad * mpf("6.371e8") / 980.665, 4), "g")
print("mass needed for Earth density 5.51 g/cm^3 to hold (rho_crit ~ 1/M^2):",
      fmt(mpf("1e8") * sqrt(rho_crit / mpf("5.51")), 4), "Msun")

print("\n== Kerr principal-null delay closed form vs quadrature, a=0.9, 1.7M -> 400M ==")
a = mpf("0.9")
rp_, rm_ = rplus(a), 1 - sqrt(1 - a * a)
closed = (400 - mpf("1.7")) + (2 / (rp_ - rm_)) * (
    rp_ * log((400 - rp_) / (mpf("1.7") - rp_)) - rm_ * log((400 - rm_) / (mpf("1.7") - rm_)))
numeric = quad(lambda r: (r * r + a * a) / (r * r - 2 * r + a * a), [mpf("1.7"), 400])
print("closed", fmt(closed, 12), "quad", fmt(numeric, 12))

print("\n== M87 scale (6.5e9 Msun): delays in days ==")
m87_s = G * mpf("6.5e9") * MSUN_G / C ** 3
print("GM/c^3 =", fmt(m87_s / DAY, 5), "d ; authority 400M radius =", fmt(400 * m87_s / DAY, 5),
      "light-days ; link 40 light-days =", fmt(40 * DAY / m87_s, 5), "M")
sch = lambda r1, r2: (r2 - r1) + 2 * log((r2 - 2) / (r1 - 2))
for r1, r2 in [(mpf(100), mpf(400)), (mpf(20), mpf(400)), (mpf(6), mpf(400))]:
    rad = sch(r1, r2) * m87_s / DAY
    chord = (r1 + r2) * m87_s / DAY
    print(f"radial {fmt(r1,4)}->{fmt(r2,4)}: {fmt(rad,5)} d ; antipodal flat chord >= {fmt(chord,5)} d")
for r in [mpf(6), mpf(20), mpf(100)]:
    print(f"same band r={fmt(r,4)}M antipodal half-circumference {fmt(pi*r*m87_s/DAY,5)} d (code: 0)")

print("\n== Transit at 0.5c: proper time per coordinate turn ==")
beta = mpf("0.5")
print("dtau/dt =", fmt(sqrt(1 - beta ** 2), 6), "; 40 ld at 0.5c = 80 coordinate d ->",
      fmt(80 * sqrt(1 - beta ** 2), 5), "proper d (code books 80)")

print("\n== Proper time a canon Miller colony accrues in a 1200-turn, 1-day-turn campaign ==")
print(fmt(1200 * DAY * f_c / 60, 5), "proper minutes")

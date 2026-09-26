import math
import numpy as np
from scipy.integrate import quad

# ---------- 1. kerrInitConsts sign of Lz (port of shader/include/kerr.glsl) ----------
def kerr_init_consts(pos, d, rs, a):
    r = np.linalg.norm(pos); cosT = pos[2]/r; sinT = math.sqrt(max(1-cosT*cosT,0)); sin2=sinT*sinT
    phi = math.atan2(pos[1], pos[0]); cP, sP = math.cos(phi), math.sin(phi)
    e_r = np.array([sinT*cP, sinT*sP, cosT]); e_th = np.array([cosT*cP, cosT*sP, -sinT]); e_ph = np.array([-sP, cP, 0])
    kr = d@e_r; kth = (d@e_th)/r; kph = (d@e_ph)/(r*sinT)
    sigma = r*r + a*a*cosT*cosT; delta = r*r - rs*r + a*a; f = rs*r/sigma
    gtt = -(1-f); gtph = -f*a*sin2; grr = sigma/abs(delta); gthth = sigma; gphph = (r*r+a*a+f*a*a*sin2)*sin2
    spatial = grr*kr*kr + gthth*kth*kth + gphph*kph*kph; hb = gtph*kph; disc = hb*hb - gtt*spatial
    sq = math.sqrt(disc); ka = (-hb+sq)/gtt; kb = (-hb-sq)/gtt; kt = ka if ka>0 else kb
    E = -(gtt*kt + gtph*kph); L = gtph*kt + gphph*kph
    return E, L/E
rs = 2.0; a = 0.9  # r_s = 2M, M = 1
cam = np.array([1000.0, 0.0, 1e-9])
d = np.array([-1.0, 0.004, 0.0]); d /= np.linalg.norm(d)
E, b_code = kerr_init_consts(cam, d, rs, a)
# physical photon arriving at camera travels along -d: L_phys = (r x p)_z with p = -d
b_phys = np.cross(cam, -d)[2] / 1.0
print(f"[1] pixel offset +y: code b = {b_code:+.4f} M, physical arriving-photon b = {b_phys:+.4f} M")

# Bardeen critical curve edges on equatorial line (i=90): xi of prograde/retrograde circular photon orbits
def photon_orbit(a, pro):
    return 2*(1+math.cos(2/3*math.acos(-a if pro else a)))
for pro in (True, False):
    r = photon_orbit(a, pro); xi = -(r**3 - 3*r*r + a*a*r + a*a)/(a*(r-1))
    print(f"    photon orbit {'pro' if pro else 'retro'} r={r:.4f} M, xi = {xi:+.4f} M")

# ---------- 2. Fe K g-factor: 1/u^t for circular equatorial Kerr orbit ----------
def ut_exact(r, a):  # BPT 1972
    return (r**1.5 + a)/(r**0.75*math.sqrt(r**1.5 - 3*r**0.5 + 2*a))
def repo_face_on_g(r, a):
    return math.sqrt(1 - 3/r + 2*a/r**1.5)
def isco(a):
    z1 = 1+(1-a*a)**(1/3)*((1+a)**(1/3)+(1-a)**(1/3)); z2 = math.sqrt(3*a*a+z1*z1)
    return 3+z2-math.sqrt((3-z1)*(3+z1+2*z2))
for aa in (0.0, 0.5, 0.9, 0.998):
    r = isco(aa)
    print(f"[2] a={aa}: r_isco={r:.4f}  face-on g exact={1/ut_exact(r,aa):.4f}  repo={repo_face_on_g(r,aa):.4f}  ratio={repo_face_on_g(r,aa)*ut_exact(r,aa):.4f}")

# ---------- 3. Novikov-Thorne / Page-Thorne flux profile vs repo's Newtonian profile ----------
def pt_flux(r, a):  # Page & Thorne 1974 via direct integral, M=1, Mdot/(4pi)=1
    def E(r):  return (r**1.5 - 2*r**0.5 + a)/(r**0.75*math.sqrt(r**1.5 - 3*r**0.5 + 2*a))
    def L(r):  return (r*r - 2*a*r**0.5 + a*a)/(r**0.75*math.sqrt(r**1.5 - 3*r**0.5 + 2*a))
    def Om(r): return 1/(r**1.5 + a)
    h = 1e-6
    dL = lambda x: (L(x+h)-L(x-h))/(2*h)
    dOm = (Om(r+h)-Om(r-h))/(2*h)
    ri = isco(a)
    I = quad(lambda x: (E(x)-Om(x)*L(x))*dL(x), ri, r)[0]
    return -dOm/((E(r)-Om(r)*L(r))**2) * I / r   # sqrt(-g) = r at equator (BL, M=1)
def newt_flux(r, a):
    ri = isco(a); x = ri/r
    return x**3*(1-math.sqrt(x))
for aa in (0.0, 0.9):
    ri = isco(aa); rr = np.linspace(ri*1.0005, 40, 20000)
    pt = np.array([pt_flux(x, aa) for x in rr]); nw = np.array([newt_flux(x, aa) for x in rr])
    print(f"[3] a={aa}: r_isco={ri:.3f}  peak r PT={rr[pt.argmax()]:.3f}  peak r repo={rr[nw.argmax()]:.3f}", end="")
    ptn = pt/pt.max(); nwn = nw/nw.max()
    for probe in (1.2, 2.0, 4.0):
        k = np.searchsorted(rr, probe*ri); print(f"  F(r={probe}r_in) PT/repo={ptn[k]/nwn[k]:.3f}", end="")
    print()

# repo thin_disk.h novikovThorneFactor vs exact Schwarzschild f (normalized so F = 3/(8 pi r^3) * f form)
def repo_ntf(r, ri):
    x = math.sqrt(r); xi = math.sqrt(ri)
    return (1 - math.sqrt(ri/r)) - (3/(2*x*x))*math.log(x/xi) - 3*(x-xi)/(x*x*xi)
for r in (7.0, 10.0, 20.0, 100.0):
    exact = pt_flux(r, 0.0) * r**3 / 1.5   # F = (3/(2 r^3)) f  with Mdot/(4pi)=1 => f = F r^3/1.5
    print(f"[3b] a=0 r={r}: exact PT f={exact:.4f}  repo novikovThorneFactor={repo_ntf(r,6.0):+.4f}")

# ---------- 4. diskDopplerBoost orbital speed vs exact ZAMO-frame speed ----------
def v_zamo(r, a):  # BPT eq. 3.10 style: v = (r^2 - 2 a sqrt r + a^2)/(sqrt(Delta)(r^1.5 + a))
    D = r*r - 2*r + a*a
    return (r*r - 2*a*math.sqrt(r) + a*a)/(math.sqrt(D)*(r**1.5 + a))
def v_repo(r, a):
    return math.sqrt(1/(r - 2 + a*math.sqrt(1/r)))
for aa in (0.0, 0.9):
    for r in (isco(aa), 6.0, 10.0):
        print(f"[4] a={aa} r={r:.3f}: v exact(ZAMO)={v_zamo(r,aa):.4f}  v repo={min(v_repo(r,aa),0.99):.4f}")

# ---------- 5. kerrTimeDilation formula in ergoregion ----------
M=1.0; a=0.9; r=1.6; th=math.pi/2
sigma=r*r; gtt=-(1-2*M*r/sigma)
print(f"[5] r={r} (r+={1+math.sqrt(1-a*a):.3f}, r_ergo(eq)=2): -g_tt={-gtt:+.3f} -> sqrt gives {'NaN' if -gtt<0 else math.sqrt(-gtt)}")
D=r*r-2*r+a*a; A=(r*r+a*a)**2-a*a*D
print(f"    ZAMO lapse sqrt(Sigma*Delta/A) = {math.sqrt(sigma*D/A):.4f}")

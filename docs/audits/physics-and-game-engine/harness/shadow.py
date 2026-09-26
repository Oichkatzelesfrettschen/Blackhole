import math, os, numpy as np
_HERE = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(_HERE, 'rcheck.py')) as _f:
    exec(_f.read().split('rs=2.0')[0])
def consts(pos, d, rs, a, fix=False):
    r = np.linalg.norm(pos); cosT = pos[2]/r; sinT = math.sqrt(max(1-cosT*cosT,0)); sin2=sinT*sinT
    phi = math.atan2(pos[1], pos[0]); cP, sP = math.cos(phi), math.sin(phi)
    e_r = np.array([sinT*cP, sinT*sP, cosT]); e_th = np.array([cosT*cP, cosT*sP, -sinT]); e_ph = np.array([-sP, cP, 0])
    kr = d@e_r; kth = (d@e_th)/r; kph = (d@e_ph)/(r*sinT)
    sigma = r*r + a*a*cosT*cosT; delta = r*r - rs*r + a*a; f = rs*r/sigma
    gtt = -(1-f); gtph = -f*a*sin2; grr = sigma/abs(delta); gthth = sigma; gphph = (r*r+a*a+f*a*a*sin2)*sin2
    spatial = grr*kr*kr + gthth*kth*kth + gphph*kph*kph; hb = gtph*kph; disc = hb*hb - gtt*spatial
    sq = math.sqrt(disc); ka = (-hb+sq)/gtt; kb = (-hb-sq)/gtt; kt = ka if ka>0 else kb
    E = -(gtt*kt + gtph*kph); L = (gtph*kt + gphph*kph)/E
    pth = sigma*kth/E
    Q = pth*pth - a*a*cosT*cosT + (L*L*cosT*cosT/sin2 if fix else L*L/sin2)
    return L, Q
def gpu_trace(cam, d, rs, a, step=0.1, maxSteps=300, maxDist=100.0, fix=False):
    L, Q = consts(cam, d, rs, a, fix)
    r = np.linalg.norm(cam); th = math.pi/2; sr = -1.0 if d@(cam/r) < 0 else 1.0
    M = rs/2; rh = M + math.sqrt(M*M - a*a)
    for i in range(maxSteps):
        if r <= rh: return 'capture'
        dh = r - rh; sh = min(max(dh/rs, 0.1), 1.0); sph = min(1.0, 0.5 + abs(r-1.5*rs)/rs); sf = min(1.0, 0.5/r)
        dl = step*min(sf, min(sh, sph))
        Delta = r*r - rs*r + a*a; A = (r*r+a*a) - a*L
        if fix:
            R = A*A - Delta*(Q + (L-a)**2 - 0.0)  # Q_std convention
        else:
            R = A*A - Delta*(Q + (L-a)**2)
        if R < 0: sr = -sr
        r += dl*sr*math.sqrt(max(R, 0.0))
        if r > maxDist: return 'escape'
    return 'maxsteps'
def exact_capture(b, a, r0):
    # physical: equatorial photon, capture iff R_std(r)>0 on (r+, r0)
    M=1; rh = M + math.sqrt(M*M-a*a)
    rr = np.linspace(rh*1.0001, r0, 20000)
    R = (rr*rr + a*a - a*b)**2 - (rr*rr - 2*rr + a*a)*(b-a)**2
    return bool(np.all(R > 0))
def edges(fn):
    ys = np.linspace(-0.9, 0.9, 3601)
    cap = [fn(y) for y in ys]
    idx = [i for i,c in enumerate(cap) if c]
    return (ys[idx[0]], ys[idx[-1]]) if idx else None
def pix(y):
    d = np.array([-1.0, y, 0.0]); return d/np.linalg.norm(d)
rs=2.0; a=0.9; r0=15.0
cam = np.array([r0, 0.0, 0.0])
gpu = edges(lambda y: gpu_trace(cam, pix(y), rs, a) == 'capture')
gpu_fix = edges(lambda y: gpu_trace(cam, pix(y), rs, a, fix=True) == 'capture')
gpu_fine = edges(lambda y: gpu_trace(cam, pix(y), rs, a, step=0.01, maxSteps=5000, fix=True) == 'capture')
# code-convention exact (b_code = +(r x d)_z -> equals physical with a->-a); physical exact: b_phys = -(r x d)_z
def bphys(y):
    d = pix(y); return -np.cross(cam, d)[2]
def bcode_exact(y):
    L,_ = consts(cam, pix(y), rs, a, True); return L
phys = edges(lambda y: exact_capture(consts(cam, -pix(y), rs, a, True)[0], a, r0))
codeconv = edges(lambda y: exact_capture(bcode_exact(y), a, r0))
sch = edges(lambda y: gpu_trace(cam, pix(y), rs, 1e-4, fix=True, step=0.01, maxSteps=5000) == 'capture')
print("tan-angle edges of capture region along equatorial scan (camera r=15M, a=0.9):")
print(" GPU scheme as shipped (Euler + Q bug, step 0.1, 300 steps):", gpu)
print(" GPU scheme, Q convention fixed, step 0.1:                ", gpu_fix)
print(" GPU scheme, Q fixed, step 0.01/5000:                     ", gpu_fine)
print(" exact, code sign convention (future ray along +dir):      ", codeconv)
print(" exact, physical backward trace (photon arriving along -dir):", phys)

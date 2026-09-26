import math, numpy as np
def init(pos, d, rs, a):
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
    Q = pth*pth - a*a*cosT*cosT + L*L/sin2
    # code R and Theta at initial point
    A = (r*r+a*a) - a*L
    Rcode = A*A - delta*(Q + (L-a)**2)
    Thcode = Q + a*a*cosT*cosT - L*L/sin2
    Rtrue = (sigma*kr/E)**2
    Qstd = pth*pth - a*a*cosT*cosT + L*L*cosT*cosT/sin2
    Rstd = A*A - delta*(Qstd + (L-a)**2)
    return dict(r=r, L=L, Q_code=Q, Q_std=Qstd, R_code=Rcode, R_std=Rstd, R_true=Rtrue, Theta_code=Thcode, Theta_true=pth*pth)
rs=2.0
for a in (0.0, 0.9):
    for pos, d in [((20,0,1e-9),(0,1,0)), ((20,0,1e-9),(-0.8,0.6,0)), ((15,3,4),(-0.7,0.2,-0.3))]:
        d = np.array(d,float); d/=np.linalg.norm(d)
        o = init(np.array(pos,float), d, rs, a)
        print(f"a={a} pos={pos} dir={np.round(d,3)}: " + "  ".join(f"{k}={v:.5g}" for k,v in o.items()))

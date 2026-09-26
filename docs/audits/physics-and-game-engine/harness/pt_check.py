import mpmath as mp
mp.mp.dps = 30
def isco(a):
    z1 = 1 + mp.cbrt(1-a*a)*(mp.cbrt(1+a)+mp.cbrt(1-a))
    z2 = mp.sqrt(3*a*a+z1*z1)
    return 3 + z2 - mp.sign(a)*mp.sqrt((3-z1)*(3+z1+2*z2)) if a!=0 else mp.mpf(6)
def closed(r,a):
    x=mp.sqrt(r); x0=mp.sqrt(isco(a))
    th=mp.acos(a)/3
    xs=[2*mp.cos(th-mp.pi/3), 2*mp.cos(th+mp.pi/3), -2*mp.cos(th)]
    s = x - x0 - mp.mpf(3)/2*a*mp.log(x/x0)
    for i in range(3):
        xi=xs[i]; xj=xs[(i+1)%3]; xk=xs[(i+2)%3]
        if abs(xi) < mp.mpf('1e-25'): continue
        s -= 3*(xi-a)**2/(xi*(xi-xj)*(xi-xk))*mp.log((x-xi)/(x0-xi))
    return s/(x**4*(x**3-3*x+2*a))
def ELO(r,a):
    x=mp.sqrt(r); Q=x**3-3*x+2*a
    E=(x**3-2*x+a)/(x**1.5*mp.sqrt(Q)); L=(x**4-2*a*x+a*a)/(x**1.5*mp.sqrt(Q)); O=1/(x**3+a)
    return E,L,O
def quad(r,a):
    ri=isco(a)
    Om=lambda rr: ELO(rr,a)[2]
    L=lambda rr: ELO(rr,a)[1]
    I=mp.quad(lambda rr: (ELO(rr,a)[0]-ELO(rr,a)[2]*ELO(rr,a)[1])*mp.diff(L,rr), [ri,r])
    E,Lr,O=ELO(r,a)
    return -(1/(4*mp.pi*r))*mp.diff(Om,r)/(E-O*Lr)**2*I
for a in [0,0.5,0.9,0.998]:
    a=mp.mpf(a); ri=isco(a)
    for f in [1.1,1.5,3,10]:
        r=ri*f; c=closed(r,a)*3/(8*mp.pi); q=quad(r,a)
        print(float(a), float(f), mp.nstr(c,12), mp.nstr(q,12), mp.nstr(c/q-1,3))
    rp=mp.findroot(lambda rr: mp.diff(lambda s: closed(s,a), rr), ri*1.3)
    print('peak', float(rp), float(rp/ri))
    print('eta', 1-ELO(ri,a)[0])
    x=mp.sqrt(ri); ut=(1+a/x**3)/mp.sqrt(1-3/ri+2*a/x**3); print('g_isco', 1/ut)

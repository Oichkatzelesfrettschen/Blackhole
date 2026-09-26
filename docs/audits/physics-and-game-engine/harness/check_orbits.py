from mpmath import mp, mpf, sqrt, cbrt, findroot
mp.dps=50
def zamo(r,a,th=mp.pi/2):
    S=r*r; D=r*r-2*r+a*a; A=(r*r+a*a)**2-a*a*D
    return sqrt(S*D/A)
def orbit(r,a,s=1):  # s=+1 prograde
    return sqrt(1-3/r+s*2*a*r**mpf(-1.5))/(1+s*a*r**mpf(-1.5))
def isco(a,s=1):
    z1=1+cbrt(1-a*a)*(cbrt(1+a)+cbrt(1-a)); z2=sqrt(3*a*a+z1*z1)
    return 3+z2-s*sqrt((3-z1)*(3+z1+2*z2))
print('zamo r6 a.9',zamo(6,mpf('0.9')),'pro',orbit(6,mpf('0.9')),'retro',orbit(6,mpf('0.9'),-1))
for a in [mpf('0.998')]:
    r=isco(a); print('a',a,'isco',r,'dil',1/orbit(r,a))
d=mpf('1.33e-14'); a=1-d; r=isco(a); print('a=1-1.33e-14 isco-1',r-1,'dil',1/orbit(r,a))

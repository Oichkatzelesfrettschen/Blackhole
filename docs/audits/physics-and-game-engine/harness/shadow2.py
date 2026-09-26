import os
_HERE = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(_HERE, 'shadow.py')) as _f:
    _SRC = _f.read().split('rs=2.0; a=0.9')[0]
__file__ = os.path.join(_HERE, 'shadow.py')
exec(_SRC)
rs=2.0; r0=15.0; cam=np.array([r0,0.0,0.0])
for a in (0.01, 0.5, 0.9, 0.99):
    shipped = edges(lambda y: gpu_trace(cam, pix(y), rs, a) == 'capture')
    fixed = edges(lambda y: gpu_trace(cam, pix(y), rs, a, fix=True) == 'capture')
    phys = edges(lambda y: exact_capture(consts(cam, -pix(y), rs, a, True)[0], a, r0))
    w = lambda e: e[1]-e[0]
    print(f"a={a}: shipped {tuple(round(float(v),4) for v in shipped)} w={w(shipped):.4f} | Q-fixed {tuple(round(float(v),4) for v in fixed)} w={w(fixed):.4f} | physical {tuple(round(float(v),4) for v in phys)} w={w(phys):.4f} | width ratio shipped/physical={w(shipped)/w(phys):.3f}")
# Schwarzschild RK4 accel path (a=0) exact check: analytic b_c=sqrt(27) M => tan-angle at r0: sin(alpha)=b_c*sqrt(1-2/r0)/r0
bc=math.sqrt(27); s=bc*math.sqrt(1-2/r0)/r0; print(f"a=0 exact half-width tan={s/math.sqrt(1-s*s):.4f}")

# Optically thin, Faraday-thick segments: alphaI*ds in {1e-3,1e-6,1e-9}, rho*ds in {10,1000}.
import mpmath as mp, random, csv
mp.mp.dps = 50
random.seed(11)
rows = []
for tauA in [1e-3, 1e-6, 1e-9]:
    for tauF in [10.0, 1000.0]:
        for _ in range(8):
            ds = 1.0
            rho = random.uniform(0.5, 1.0) * tauF; th = random.uniform(0, 1.0)
            rhoV, rhoQ = rho * mp.cos(th * mp.pi / 2), rho * mp.sin(th * mp.pi / 2)
            aI = tauA * random.uniform(0.5, 1.0); frac = random.uniform(0.0, 0.9); ang = random.uniform(0, 2 * mp.pi)
            aQ, aV = aI * frac * mp.cos(ang), aI * frac * mp.sin(ang)
            jI = random.uniform(0.1, 1.0); jQ = jI * random.uniform(-0.5, 0.5); jU = jI * random.uniform(-0.3, 0.3); jV = jI * random.uniform(-0.1, 0.1)
            S0 = [random.uniform(0.5, 1.0), random.uniform(-0.3, 0.3), random.uniform(-0.3, 0.3), random.uniform(-0.1, 0.1)]
            vals = [float(v) for v in (aI, aQ, aV, rhoV, rhoQ, jI, jQ, jU, jV)] + S0
            aI, aQ, aV, rhoV, rhoQ, jI, jQ, jU, jV = (mp.mpf(v) for v in vals[:9])
            K = mp.matrix([[aI, aQ, 0, aV], [aQ, aI, rhoV, 0], [0, -rhoV, aI, rhoQ], [aV, 0, -rhoQ, aI]])
            A = mp.zeros(5, 5)
            for i in range(4):
                for j in range(4):
                    A[i, j] = -K[i, j] * ds
            for i, jv in enumerate((jI, jQ, jU, jV)):
                A[i, 4] = jv * ds
            y = mp.expm(A) * mp.matrix([mp.mpf(v) for v in S0] + [1])
            rows.append([tauA * 1e6 + tauF, ds] + vals + [mp.nstr(y[i], 30) for i in range(4)])
with open("ref_thin.csv", "w", newline="") as f:
    csv.writer(f).writerows(rows)
print(len(rows))

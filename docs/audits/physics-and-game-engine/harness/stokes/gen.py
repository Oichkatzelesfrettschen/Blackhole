# Reference: exact solution of dS/ds = J - K S over one constant-coefficient
# segment via mpmath expm of the augmented 5x5 generator, 40 digits.
import mpmath as mp, random, csv
mp.mp.dps = 40
random.seed(7)
rows = []
for tauF in [0.01, 0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 100.0, 1000.0]:
    for _ in range(12):
        ds = 1.0
        rho = random.uniform(0.2, 1.0) * tauF          # total Faraday depth over the step
        th = random.uniform(0, 1.0)
        rhoV, rhoQ = rho * mp.cos(th * mp.pi / 2), rho * mp.sin(th * mp.pi / 2)
        aI = random.uniform(0.01, 2.0)
        frac = random.uniform(0.0, 0.9)                 # |eta| <= aI (positivity)
        ang = random.uniform(0, 2 * mp.pi)
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
        E = mp.expm(A)
        x = mp.matrix([mp.mpf(v) for v in S0] + [1])
        y = E * x
        rows.append([tauF, ds] + vals + [mp.nstr(y[i], 25) for i in range(4)])
with open("ref.csv", "w", newline="") as f:
    csv.writer(f).writerows(rows)
print(len(rows))

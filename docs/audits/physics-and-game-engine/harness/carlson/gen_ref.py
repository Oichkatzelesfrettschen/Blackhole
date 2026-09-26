import mpmath as mp, random, csv
mp.mp.dps = 40
random.seed(20260925)
rows = []
def lu(lo, hi): return 10 ** random.uniform(lo, hi)
# generic log-uniform triples
for _ in range(400):
    x, y, z, p = lu(-3, 3), lu(-3, 3), lu(-3, 3), lu(-3, 3)
    rows.append(("gen", x, y, z, p))
# complete-integral style arguments (0, 1-k^2, 1), k -> 1
for k in [0.1, 0.3, 0.5, 0.7, 0.9, 0.99, 0.999, 0.9999, 0.99999, 0.999999]:
    for n in [0.1, 0.5, 0.9]:
        rows.append(("Kk", 0.0, 1.0 - k * k, 1.0, 1.0 - n))
# incomplete style (cos^2 phi, 1-k^2 sin^2 phi, 1)
for _ in range(200):
    phi = random.uniform(0.01, 1.55); k = random.uniform(0.0, 0.9999); n = random.uniform(0.0, 0.95)
    s, c = mp.sin(phi), mp.cos(phi)
    x = float(c * c); y = float(1 - k * k * s * s)
    rows.append(("inc", x, y, 1.0, float(1 - n * s * s)))
with open("ref.csv", "w", newline="") as f:
    w = csv.writer(f)
    for tag, x, y, z, p in rows:
        X, Y, Z, P = (mp.mpf(repr(v)) for v in (x, y, z, p))
        rf = mp.elliprf(X, Y, Z); rd = mp.elliprd(X, Y, Z); rj = mp.elliprj(X, Y, Z, P)
        w.writerow([tag, repr(x), repr(y), repr(z), repr(p), mp.nstr(rf, 25), mp.nstr(rd, 25), mp.nstr(rj, 25)])
print(len(rows))

# Block quantization of a GRMHD-like log-density field at equal bit budget.
# A: per-block affine uniform quant (min/max), B: TurboQuant-style random rotation
# D1*H*D2 + Lloyd-Max Gaussian codebook scaled by block RMS, C: same without random signs,
# D: plain WHT energy compaction + global variance-driven bit allocation.
import numpy as np
from scipy.linalg import hadamard
from scipy.stats import norm
rng = np.random.default_rng(1234)
N = 64
k = np.fft.fftfreq(N) * N
kx, ky, kz = np.meshgrid(k, k, k, indexing="ij")
kk = np.sqrt(kx**2 + ky**2 + kz**2); kk[0, 0, 0] = 1
amp = kk ** (-11.0 / 6.0); amp[0, 0, 0] = 0          # Kolmogorov 3D: P(k) ~ k^-11/3
g = np.real(np.fft.ifftn(amp * np.fft.fftn(rng.standard_normal((N, N, N)))))
field = g / g.std() * 1.5                              # ln(rho), sigma = 1.5
B = 4
blocks = field.reshape(N//B, B, N//B, B, N//B, B).transpose(0, 2, 4, 1, 3, 5).reshape(-1, B**3)
d = B**3
H = hadamard(d) / np.sqrt(d)
def lloyd_max(bits, iters=200):
    L = 2**bits; c = norm.ppf((np.arange(L) + 0.5) / L)
    for _ in range(iters):
        t = np.concatenate(([-np.inf], (c[1:] + c[:-1]) / 2, [np.inf]))
        a, b = t[:-1], t[1:]
        c = (norm.pdf(a) - norm.pdf(b)) / (norm.cdf(b) - norm.cdf(a))
    return c
def qnear(x, cb):
    return cb[np.abs(x[..., None] - cb).argmin(-1)]
def fp16(x): return x.astype(np.float16).astype(np.float64)
def rmse(a): return np.sqrt(np.mean((a - blocks) ** 2)) / blocks.std()
out = {}
for bits in (2, 3, 4, 6):
    # A: affine per block, overhead 2 x fp16 per block
    lo, hi = fp16(blocks.min(1)), fp16(blocks.max(1))
    s = np.maximum(hi - lo, 1e-12)
    L = 2**bits - 1
    qa = lo[:, None] + np.round(np.clip((blocks - lo[:, None]) / s[:, None], 0, 1) * L) / L * s[:, None]
    cb = lloyd_max(bits)
    def rot(signs):
        d1, d2 = signs
        mu = fp16(blocks.mean(1)); x = blocks - mu[:, None]
        y = (x * d2) @ H.T * d1
        sc = fp16(np.sqrt(np.mean(y**2, 1)) + 1e-12)
        yq = qnear(y / sc[:, None], cb) * sc[:, None]
        return ((yq * d1) @ H) * d2 + mu[:, None]
    ones = (np.ones(d), np.ones(d))
    rs = (rng.choice([-1.0, 1.0], d), rng.choice([-1.0, 1.0], d))
    qb, qc = rot(rs), rot(ones)
    # D: WHT compaction with global per-coefficient bit allocation (reverse water-filling),
    # total bits per block = bits*d; codebooks are global (no per-block overhead).
    Y = blocks @ H.T
    var = Y.var(0) + 1e-18
    total = bits * d
    lam_lo, lam_hi = 1e-12, var.max()
    for _ in range(100):
        lam = np.sqrt(lam_lo * lam_hi)
        bi = np.maximum(0, np.round(0.5 * np.log2(var / lam)))
        if bi.sum() > total: lam_lo = lam
        else: lam_hi = lam
    bi = np.maximum(0, np.round(0.5 * np.log2(var / lam_hi))).astype(int)
    mu_c = Y.mean(0)
    Yq = np.empty_like(Y)
    for i in range(d):
        if bi[i] == 0: Yq[:, i] = mu_c[i]
        else: Yq[:, i] = mu_c[i] + qnear((Y[:, i] - mu_c[i]) / np.sqrt(var[i]), lloyd_max(min(bi[i], 10))) * np.sqrt(var[i])
    qd = Yq @ H
    print(f"bits/value={bits} (+0.5 overhead A/B/C, D uses {bi.sum()/d:.2f}): "
          f"A affine {rmse(qa):.4f} | B rot+LM {rmse(qb):.4f} | C WHT+LM (no signs) {rmse(qc):.4f} | D WHT alloc {rmse(qd):.4f}")
print("fp16 direct (16 bits/value):", f"{rmse(fp16(blocks)):.2e}")

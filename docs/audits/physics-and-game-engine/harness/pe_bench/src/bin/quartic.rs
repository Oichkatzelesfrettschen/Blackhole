use num_complex::Complex64 as C;
use pathion_ellip::quartic::{kerr_radial_potential_coefficients, solve_quartic};
fn main() {
    let (m, a) = (1.0f64, 0.9f64);
    let r = |v: f64| C::new(v, 0.0);
    let mut bad = 0; let mut n = 0; let mut worst_res: f64 = 0.0;
    for k in 0..=40 {
        let rr = 1.56 + (3.90 - 1.56) * k as f64 / 40.0;
        let delta = rr * rr - 2.0 * m * rr + a * a;
        let xi = (rr * rr * (rr - 3.0 * m) + a * a * (rr + m)) / (a * (rr - m));
        let eta = rr.powi(3) * (4.0 * m * delta - rr * (rr - m).powi(2)) / (a * a * (rr - m).powi(2));
        let (ca, cb, cc, cd) = kerr_radial_potential_coefficients(r(m), r(a), r(xi), r(eta));
        let roots = solve_quartic(ca, cb, cc, cd);
        let poly = |z: C| z.powi(4) + ca * z.powi(3) + cb * z * z + cc * z + cd;
        let scale = 1.0 + cb.norm() + cc.norm() + cd.norm();
        let res = roots.iter().map(|z| poly(*z).norm() / (scale * (1.0 + z.norm().powi(4)))).fold(0.0, f64::max);
        let best = roots.iter().map(|z| (z - r(rr)).norm()).fold(f64::INFINITY, f64::min) / rr;
        n += 1; if best > 1e-6 { bad += 1; }
        worst_res = worst_res.max(res);
        if k % 8 == 0 || best > 1e-3 { println!("r_ph={rr:.3} eta={eta:.3} xi={xi:.3} dist_to_double_root={best:.2e} max_scaled_residual={res:.2e} roots={:?}", roots.iter().map(|z| (format!("{:.4}", z.re), format!("{:.4}", z.im))).collect::<Vec<_>>()); }
    }
    println!("points={n} double-root-missed(>1e-6)={bad} worst_scaled_residual={worst_res:.2e}");
}

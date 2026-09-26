use num_complex::Complex64 as C;
use pathion_ellip::carlson::{carlson_rf_complex, carlson_rd_complex, carlson_rj_complex};
use pathion_ellip::quartic::{kerr_radial_potential_coefficients, solve_quartic};
use std::time::Instant;
fn main() {
    let txt = std::fs::read_to_string("../carlson/ref.csv").unwrap();
    let rows: Vec<Vec<f64>> = txt.lines().map(|l| l.split(',').skip(1).map(|s| s.parse().unwrap()).collect()).collect();
    let r = |v: f64| C::new(v, 0.0);
    let mut e = [Vec::new(), Vec::new(), Vec::new()];
    let mut mx_im: f64 = 0.0;
    for w in &rows {
        let f = carlson_rf_complex(r(w[0]), r(w[1]), r(w[2]));
        let d = carlson_rd_complex(r(w[0]), r(w[1]), r(w[2]));
        let j = carlson_rj_complex(r(w[0]), r(w[1]), r(w[2]), r(w[3]));
        e[0].push(((f.re - w[4]) / w[4]).abs());
        e[1].push(((d.re - w[5]) / w[5]).abs());
        e[2].push(((j.re - w[6]) / w[6]).abs());
        mx_im = mx_im.max(f.im.abs()).max(d.im.abs()).max(j.im.abs());
    }
    for (name, v) in ["RF", "RD", "RJ"].iter().zip(e.iter_mut()) {
        v.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!("pathion_ellip {name} max_rel={:.3e} median_rel={:.3e} nan={}", v.last().unwrap(), v[v.len() / 2], v.iter().filter(|x| x.is_nan()).count());
    }
    println!("max |imag| on real inputs = {mx_im:.3e}");
    let reps = 2000;
    for (name, which) in [("RF", 0), ("RD", 1), ("RJ", 2)] {
        let mut ts = Vec::new();
        for _ in 0..5 {
            let t0 = Instant::now();
            let mut sink = C::new(0.0, 0.0);
            for _ in 0..reps {
                for w in &rows {
                    sink += match which {
                        0 => carlson_rf_complex(r(w[0]), r(w[1]), r(w[2])),
                        1 => carlson_rd_complex(r(w[0]), r(w[1]), r(w[2])),
                        _ => carlson_rj_complex(r(w[0]), r(w[1]), r(w[2]), r(w[3])),
                    };
                }
            }
            std::hint::black_box(sink);
            ts.push(t0.elapsed().as_nanos() as f64 / (reps * rows.len()) as f64);
        }
        ts.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!("pathion_ellip {name} ns/call (median of 5) = {:.1}", ts[2]);
    }
    // Quartic: Kerr radial potential, Bardeen critical curve (a=0.9) roots check.
    let (m, a) = (1.0f64, 0.9f64);
    let mut worst: f64 = 0.0;
    for k in 1..200 {
        let rr = 1.5 + 2.5 * k as f64 / 200.0;
        let delta = rr * rr - 2.0 * m * rr + a * a;
        let xi = (rr * rr * (rr - 3.0 * m) + a * a * (rr + m)) / (a * (rr - m));
        let eta = rr.powi(3) * (4.0 * m * delta - rr * (rr - m).powi(2)) / (a * a * (rr - m).powi(2));
        let (ca, cb, cc, cd) = kerr_radial_potential_coefficients(r(m), r(a), r(xi), r(eta));
        let roots = solve_quartic(ca, cb, cc, cd);
        // the critical curve has a double root at r=rr
        let best = roots.iter().map(|z| (z - r(rr)).norm()).fold(f64::INFINITY, f64::min);
        worst = worst.max(best / rr);
    }
    println!("quartic: worst relative distance to double root on Kerr a=0.9 critical curve = {worst:.3e}");
}

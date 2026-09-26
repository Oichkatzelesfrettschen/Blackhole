use gr_core::energy_conserving::{FullGeodesicState, compute_energy, compute_angular_momentum, energy_conserving_step, rk4_geodesic_step};
use gr_core::kerr::{Kerr, trace_null_geodesic};
use gr_core::metric::SpacetimeMetric;
use gr_core::null_constraint::null_constraint;
use gr_core::{kerr_de_sitter as kds, kerr_newman as kn, novikov_thorne as nt, synchrotron as sy, doppler as dp};
use std::f64::consts::FRAC_PI_2;
use std::time::Instant;

fn main() {
    {
        // sedenion_homotopy_step at a=0: photon moving tangentially at r=10 (vr=0 initially has no radial pull in GR? use vr=-0.1)
        let k0 = Kerr::new(1.0, 0.0);
        let (mut r, mut th, mut vr, mut vth) = (10.0_f64, FRAC_PI_2, -0.1_f64, 0.0_f64);
        let vr0 = vr;
        for _ in 0..1000 { let o = gr_core::sedenion_geodesic::sedenion_homotopy_step(&k0, r, th, vr, vth, 0.01); r = o.0; th = o.1; vr = o.2; vth = o.3; }
        println!("sedenion_homotopy_step a=0, 1000 steps: vr {vr0} -> {vr:.12} (GR radial acceleration at r=10 is nonzero), r -> {r:.6}");
    }
    { let msun = 1.98847e33_f64; let (m1, m2) = (30.0 * msun, 30.0 * msun); let mc = gr_core::gravitational_waves::chirp_mass(m1, m2); for f in [20.0, 100.0] { println!("GW phase_2p5pn(30+30 Msun, f={f}) = {:.6e} rad (mc={:.6e} g)", gr_core::gravitational_waves::phase_2p5pn(mc, 0.25, f, 0.0, 0.0), mc); } }
    for a in [0.0, 0.5, 0.9, 0.998, -0.9] {
        let k = Kerr::new(1.0, a);
        println!(
            "Kerr a={a}: r+={:.10} r-={:.10} ergo_eq={:.6} isco_pro={:.10} isco_ret={:.10} rph_pro={:.10} rph_ret={:.10} nt::isco_radius={:.10} eta={:.8}",
            k.outer_horizon(), k.inner_horizon(), k.ergosphere_radius(FRAC_PI_2), k.isco_prograde(), k.isco_retrograde(),
            k.photon_orbit_prograde(), k.photon_orbit_retrograde(), nt::isco_radius(a), nt::radiative_efficiency(a)
        );
    }
    println!("nt::disk_temperature(9, 0, 0.1, 4e6) = {:.6e} K", nt::disk_temperature(9.0, 0.0, 0.1, 4.0e6));
    for r in [6.0, 10.0] {
        let g = nt::disk_redshift_factor(r);
        let d = nt::disk_doppler_factor(r, FRAC_PI_2, FRAC_PI_2);
        // exact Schwarzschild circular orbit, photon emitted along velocity in static frame
        let v: f64 = (1.0 / (r - 2.0)).sqrt();
        let exact = (1.0 - 3.0 / r).sqrt() / (1.0 - v);
        println!("nt::disk g*delta r={r}: repo={:.6} exact_local={:.6} ratio^4={:.4}", g * d, exact, (g * d / exact).powi(4));
    }
    println!("dp::disk_doppler_boost(r=1.5,a=0.998,phi=0,i=pi/2,alpha=0) = {:.4}", dp::disk_doppler_boost(1.5, 0.998, 0.0, FRAC_PI_2, 0.0));
    for x in [0.01, 0.1, 1.0, 3.0, 10.0] {
        println!("sy::synchrotron_f({x}) = {:.6}  g = {:.6}", sy::synchrotron_f(x), sy::synchrotron_g(x));
    }
    println!("kn::isco_prograde(1,0,0.5)={:.6} (1,0,0.9)={:.6}; kn::frame_dragging_omega(3,pi/2,1,0.5,0.5)={:.6}; kn::potential_phi(3,pi/2,0.5,0.5)={:.6}",
        kn::isco_prograde(1.0, 0.0, 0.5), kn::isco_prograde(1.0, 0.0, 0.9), kn::frame_dragging_omega(3.0, FRAC_PI_2, 1.0, 0.5, 0.5), kn::potential_phi(3.0, FRAC_PI_2, 0.5, 0.5));
    for l in [1e-4, 1e-2, 0.1] {
        println!("kds L={l}: event(a=0.9)={:.6} inner={:.6} cosmo={:.6} event(a=0)={:.6}", kds::event_horizon(1.0, 0.9, l), kds::inner_horizon(1.0, 0.9, l), kds::cosmological_horizon(l), kds::event_horizon(1.0, 0.0, l));
    }

    // Polar turning point test: gr_core trace_null_geodesic with a=0.9, E=1, L=2, Q=10.
    let (a, e, l, q) = (0.9_f64, 1.0_f64, 2.0_f64, 10.0_f64);
    let res = trace_null_geodesic(a, e, l, q, 40.0, FRAC_PI_2, 200.0, -1.0, 1.0, 20000);
    let max_cos = res.theta.iter().map(|t| t.cos().abs()).fold(0.0_f64, f64::max);
    // true null: Theta = Q + a^2 E^2 c^2 - L^2 c^2/(1-c^2) = 0  -> solve for c^2
    let solve = |extra: f64| {
        // Q (1-c2) + extra c2 (1-c2) - L^2 c2 = 0, extra = a^2 E^2 (null) or -a^2 (1-E^2) (repo)
        let (aa, bb, cc) = (-extra, extra - q - l * l, q);
        let disc = bb * bb - 4.0 * aa * cc;
        if aa.abs() < 1e-15 { -cc / bb } else { let r1 = (-bb - disc.sqrt()) / (2.0 * aa); let r2 = (-bb + disc.sqrt()) / (2.0 * aa); if (0.0..=1.0).contains(&r1) { r1 } else { r2 } }
    };
    println!("trace_null_geodesic polar turning |cos|max={:.6}; true-null prediction={:.6}; repo-Theta prediction={:.6}; samples={} reason={}",
        max_cos, solve(a * a * e * e).sqrt(), solve(-a * a * (1.0 - e * e)).sqrt(), res.theta.len(), res.termination_reason);

    // Energy-conserving integrator on Kerr a=0.9 near-critical equatorial ray, affine parameter.
    let k = Kerr::new(1.0, 0.9);
    let rph = 1.5578546274233827_f64;
    let bc = -(rph.powi(3) - 3.0 * rph * rph + a * a * rph + a * a) / (a * (rph - 1.0));
    let b = bc * 1.001;
    let x0 = [0.0, 50.0, FRAC_PI_2, 0.0];
    let g0 = k.metric_components(&x0);
    let gi = k.inverse_metric(&x0);
    // p_t = -1, p_phi = b ; raise
    let vt = gi[0][0] * (-1.0) + gi[0][3] * b;
    let vph = gi[3][0] * (-1.0) + gi[3][3] * b;
    let rest = -(g0[0][0] * vt * vt + 2.0 * g0[0][3] * vt * vph + g0[3][3] * vph * vph);
    let vr = -(rest / g0[1][1]).sqrt();
    for (name, corrected) in [("rk4", false), ("energy_conserving", true)] {
        let mut s = FullGeodesicState { x: x0, v: [vt, vr, 0.0, vph] };
        let e0 = compute_energy(&g0, &s.v);
        let l0 = compute_angular_momentum(&g0, &s.v);
        let h = 0.01;
        let t0 = Instant::now();
        let mut n = 0;
        let mut rmin = 1e9_f64;
        let mut max_norm = 0.0_f64;
        while n < 200000 {
            s = if corrected {
                energy_conserving_step(&s, h, |x| k.metric_components(x), |x| k.christoffel(x), 0.0)
            } else {
                rk4_geodesic_step(&s, h, |x| k.metric_components(x), |x| k.christoffel(x))
            };
            n += 1;
            rmin = rmin.min(s.x[1]);
            let g = k.metric_components(&s.x);
            max_norm = max_norm.max(null_constraint(&g, &s.v).abs());
            if s.x[1] > 60.0 || s.x[1] < k.outer_horizon() * 1.001 { break; }
        }
        let dt = t0.elapsed().as_nanos() as f64 / n as f64;
        let g = k.metric_components(&s.x);
        let e1 = compute_energy(&g, &s.v);
        let l1 = compute_angular_momentum(&g, &s.v);
        println!("{name}: steps={n} rmin={rmin:.6} final r={:.3} |dE/E|={:.3e} |dL/L|={:.3e} max|null norm|={:.3e} ns/step(incl. norm check)={dt:.1}",
            s.x[1], ((e1 - e0) / e0).abs(), ((l1 - l0) / l0).abs(), max_norm);
    }
}

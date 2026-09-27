"""Generate canon-spin turning rays from 50-digit Kerr potentials."""

import csv
from pathlib import Path

import mpmath

mpmath.mp.dps = 50
M = mpmath.mpf
EPSILON = M('1.33e-14')
X_OBSERVER = M('3.7611284825013188359e-5')
SPIN = 1 - EPSILON
HORIZON = mpmath.sqrt(EPSILON * (2 - EPSILON))
RADIUS = 1 + X_OBSERVER
DELTA = (X_OBSERVER - HORIZON) * (X_OBSERVER + HORIZON)
BIG_A = RADIUS**4 + SPIN**2 * RADIUS**2 + 2 * SPIN**2 * RADIUS
ALPHA = RADIUS * mpmath.sqrt(DELTA) / mpmath.sqrt(BIG_A)
OMEGA = 2 * SPIN * RADIUS / BIG_A
VARPI = mpmath.sqrt(BIG_A) / RADIUS


def potential(offset, energy, momentum):
    radial = ((1 + offset)**2 + SPIN**2) * energy - SPIN * momentum
    return radial**2 - (offset - HORIZON) * (offset + HORIZON) * (momentum - SPIN * energy)**2


rows = []
for target in ('2.8e-7', '3.0e-7', '3.2e-7', '4.0e-7'):
    turning = M(target)
    root_delta = mpmath.sqrt((turning - HORIZON) * (turning + HORIZON))
    impact = SPIN + (1 + turning)**2 / (SPIN + root_delta)
    azimuth = ALPHA * impact / (VARPI * (1 - OMEGA * impact))
    radial = -mpmath.sqrt(1 - azimuth**2)
    radial_double = float(radial)
    azimuth_double = float(azimuth)
    energy = ALPHA + OMEGA * VARPI * M(repr(azimuth_double))
    momentum = VARPI * M(repr(azimuth_double))
    actual_root = mpmath.findroot(lambda offset: potential(offset, energy, momentum),
                                  (turning * M('0.99'), turning * M('1.01')))
    assert HORIZON < actual_root < X_OBSERVER
    assert potential((actual_root + HORIZON) / 2, energy, momentum) < 0
    assert potential((actual_root + X_OBSERVER) / 2, energy, momentum) > 0
    rows.append((target, repr(radial_double), repr(azimuth_double),
                 mpmath.nstr(actual_root, 25), '1', '1'))

with Path('tests/kerr_observer_turning_reference.csv').open('w', newline='', encoding='ascii') as output:
    writer = csv.writer(output, lineterminator='\n')
    writer.writerow(('target_x', 'radial_direction', 'azimuth_direction', 'root_x',
                     'escapes', 'from_infinity'))
    writer.writerows(rows)

with Path('tests/kerr_observer_extreme_reference.csv').open('w', newline='', encoding='ascii') as output:
    writer = csv.writer(output, lineterminator='\n')
    writer.writerow(('epsilon', 'x', 'alpha', 'omega', 'varpi', 'potential_at_x_1'))
    epsilon = M('0.1')
    x = M('1e78')
    spin = 1 - epsilon
    radius = 1 + x
    delta = (x - mpmath.sqrt(epsilon * (2 - epsilon))) * (x + mpmath.sqrt(epsilon * (2 - epsilon)))
    big_a = radius**4 + spin**2 * radius**2 + 2 * spin**2 * radius
    writer.writerow(('0.1', '1e78', mpmath.nstr(radius * mpmath.sqrt(delta / big_a), 25),
                     mpmath.nstr(2 * spin * radius / big_a, 25),
                     mpmath.nstr(mpmath.sqrt(big_a) / radius, 25), '0'))
    epsilon = M('0')
    x = M('1e-160')
    radius = 1 + x
    delta_root = x
    big_a = radius**4 + radius**2 + 2 * radius
    energy = radius * delta_root / mpmath.sqrt(big_a)
    theta_momentum = radius
    potential_at_two = (5 * energy)**2 - (theta_momentum**2 + energy**2)
    writer.writerow(('0', '1e-160', mpmath.nstr(energy, 25),
                     mpmath.nstr(2 * radius / big_a, 25),
                     mpmath.nstr(mpmath.sqrt(big_a) / radius, 25),
                     mpmath.nstr(potential_at_two, 25)))

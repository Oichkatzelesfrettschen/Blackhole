/*
 * Single source for the synchrotron G(x) LUT domain.
 *
 * Included by C++ (src/physics/synchrotron.h, src/gpu/lut_texture.h),
 * CUDA (src/cuda/device_physics.cuh), and GLSL
 * (shader/include/synchrotron_emission.glsl via the shader include
 * preprocessor). These values previously lived as independent literals
 * in all four files behind a "change all three together" comment.
 *
 * Preprocessor-only on purpose: plain #define is the intersection all
 * three languages accept. Unsuffixed literals parse as float in GLSL
 * and as double in C++/CUDA; each consumer converts to its own type.
 *
 * Copyright (c) 2026 Terascale Functionalists
 * SPDX-License-Identifier: MIT
 */
#ifndef SYNCHROTRON_LUT_DOMAIN_H
#define SYNCHROTRON_LUT_DOMAIN_H

/* Log-spaced domain bounds for the G(x) = x*K_{2/3}(x) lookup table.
 * Below X_MIN the small-x asymptote 1.3541*x^(1/3) is exact enough;
 * above X_MAX the large-x asymptote sqrt(pi/2)*sqrt(x)*exp(-x) is. */
#define SYNCH_G_LUT_DOMAIN_X_MIN 0.001
#define SYNCH_G_LUT_DOMAIN_X_MAX 30.0

/* Entry count of the 1D LUT texture (log-spaced R32F). */
#define SYNCH_G_LUT_DOMAIN_ENTRIES 256

#endif /* SYNCHROTRON_LUT_DOMAIN_H */

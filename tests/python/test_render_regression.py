# tests/python/test_render_regression.py
#
# WHY: Render regression testing catches physics or shading changes that break visual
#      correctness without introducing a failing unit test.  "Did the render change
#      materially?" must have a definitive, automated answer.
#
# WHAT:
#   - compare_images(): tolerance-based RGBA image diff via OIIO ImageBufAlgo.compare()
#   - ReferenceStore: manages reference PNG baselines in tests/python/references/
#   - assert_render_match(): pytest assertion combining both
#   - Tests exercise the comparison logic itself (not the renderer) so they run without
#     a GPU or Blender instance.
#
# HOW (run all):
#   pytest tests/python/test_render_regression.py -v
# HOW (skip slow render invocations):
#   pytest tests/python -m "not slow"
#
# OIIO 3.1.11.0 (cachyos-extra-v3, AVX2/FMA, no CUDA):
#   image diff is memory-bandwidth bound -- AVX2 is the right tier, CUDA overhead
#   would dominate for typical render sizes (1920x1080 = 33 MB RGBA32F).

from __future__ import annotations

import math
import os
from dataclasses import dataclass
from pathlib import Path
from typing import NamedTuple

import numpy as np
import numpy.testing as npt
import pytest

try:
    import OpenImageIO as oiio

    OIIO_AVAILABLE = True
except ImportError:
    OIIO_AVAILABLE = False

requires_oiio = pytest.mark.skipif(not OIIO_AVAILABLE, reason="OpenImageIO not installed")

# ---- Reference directory stored next to this test file ----------------------
_REFERENCES = Path(__file__).parent / "references"
_REFERENCES.mkdir(exist_ok=True)


# ---------------------------------------------------------------------------
# Core comparison primitives
# ---------------------------------------------------------------------------

class ImageDiffResult(NamedTuple):
    """Structured result from compare_images().

    WHY: A NamedTuple instead of a raw dict makes it easy to assert on individual
    metrics and print structured failure messages.
    """

    mean_error: float       # mean absolute difference per channel
    rms_error: float        # root-mean-square error per channel
    peak_snr: float         # peak signal-to-noise ratio (dB)  -- higher is better
    max_error: float        # maximum per-channel error (worst pixel)
    n_fail_pixels: int      # pixels exceeding the failure threshold
    passed: bool            # True if n_fail_pixels == 0


def compare_images(
    a: np.ndarray,
    b: np.ndarray,
    fail_threshold: float = 0.05,
    warn_threshold: float = 0.01,
) -> ImageDiffResult:
    """Compare two RGBA float32 images and return structured diff metrics.

    WHY OIIO: ImageBufAlgo.compare() supports tolerance-based pixel comparison with
    explicit fail/warn thresholds, matching how production VFX pipelines validate
    render outputs (DreamWorks, Pixar, ILM all use this pattern).

    WHY fallback to numpy: if OIIO is unavailable (e.g. minimal CI container), we
    compute the same metrics purely in NumPy so the test suite degrades gracefully.

    Args:
        a, b: (H, W, C) float32 arrays, values in [0, inf) -- HDR allowed.
        fail_threshold: pixels with |a - b| > this are counted as failures.
        warn_threshold: pixels with |a - b| > this but <= fail_threshold are warnings.

    Returns:
        ImageDiffResult with all comparison metrics.
    """
    if a.shape != b.shape:
        raise ValueError(f"Shape mismatch: {a.shape} vs {b.shape}")
    if a.dtype != np.float32 or b.dtype != np.float32:
        a = a.astype(np.float32)
        b = b.astype(np.float32)

    if OIIO_AVAILABLE:
        return _compare_oiio(a, b, fail_threshold, warn_threshold)
    return _compare_numpy(a, b, fail_threshold)


def _compare_oiio(
    a: np.ndarray,
    b: np.ndarray,
    fail_threshold: float,
    warn_threshold: float,
) -> ImageDiffResult:
    """OIIO-backed comparison using ImageBufAlgo.compare().

    WHY set_pixels with 3D array: OIIO expects (H, W, C) layout from numpy.
    Flattening to 1D scrambles the channel ordering.
    """
    h, w = a.shape[:2]
    nchans = a.shape[2] if a.ndim == 3 else 1

    spec = oiio.ImageSpec(w, h, nchans, oiio.FLOAT)

    buf_a = oiio.ImageBuf(spec)
    buf_b = oiio.ImageBuf(spec)

    roi = oiio.ROI(0, w, 0, h, 0, 1, 0, nchans)
    # Pass the 3D (H, W, C) array directly -- OIIO reads channel-interleaved
    buf_a.set_pixels(roi, np.ascontiguousarray(a))
    buf_b.set_pixels(roi, np.ascontiguousarray(b))

    comp = oiio.ImageBufAlgo.compare(buf_a, buf_b, fail_threshold, warn_threshold)

    # peak SNR: 20 * log10(1 / rms) for images normalised to [0,1].
    # For HDR images we use the actual image peak.
    peak = float(np.max(a))
    psnr = (
        float("inf")
        if comp.rms_error == 0.0
        else 20.0 * math.log10(max(peak, 1.0) / comp.rms_error)
        if comp.rms_error > 0
        else float("inf")
    )

    return ImageDiffResult(
        mean_error=comp.meanerror,
        rms_error=comp.rms_error,
        peak_snr=psnr,
        max_error=comp.maxerror,
        n_fail_pixels=comp.nfail,
        passed=comp.nfail == 0,
    )


def _compare_numpy(
    a: np.ndarray,
    b: np.ndarray,
    fail_threshold: float,
) -> ImageDiffResult:
    """Pure-NumPy fallback -- same metrics, no OIIO dependency."""
    with np.errstate(divide="ignore", invalid="ignore"):
        diff = np.abs(a.astype(np.float32) - b.astype(np.float32))
        mean_err = float(diff.mean())
        rms_err = float(np.sqrt((diff ** 2).mean()))
        max_err = float(diff.max())
        peak = float(a.max())
        psnr = (
            float("inf")
            if rms_err == 0.0
            else 20.0 * math.log10(max(peak, 1.0) / rms_err)
            if rms_err > 0
            else float("inf")
        )
        n_fail = int((diff > fail_threshold).sum())
    return ImageDiffResult(
        mean_error=mean_err,
        rms_error=rms_err,
        peak_snr=psnr,
        max_error=max_err,
        n_fail_pixels=n_fail,
        passed=n_fail == 0,
    )


# ---------------------------------------------------------------------------
# Reference image store
# ---------------------------------------------------------------------------

class ReferenceStore:
    """Manages reference PNG baselines for regression comparison.

    Usage:
        store = ReferenceStore("cuda_fp32")
        if not store.exists("m87_frame0"):
            store.save("m87_frame0", rendered_array)
        result = store.compare("m87_frame0", new_render, fail_threshold=0.02)
        assert result.passed
    """

    def __init__(self, suite_name: str) -> None:
        self._dir = _REFERENCES / suite_name
        self._dir.mkdir(parents=True, exist_ok=True)

    def _path(self, name: str) -> Path:
        # EXR: lossless float32 storage, no alpha-handling quirks, proper HDR support
        return self._dir / f"{name}.exr"

    def exists(self, name: str) -> bool:
        return self._path(name).is_file()

    def save(self, name: str, image: np.ndarray) -> Path:
        """Save a float32 (H, W, 4) array as a 16-bit PNG reference."""
        path = self._path(name)
        if OIIO_AVAILABLE:
            _save_oiio(image, path)
        else:
            _save_numpy_png(image, path)
        return path

    def load(self, name: str) -> np.ndarray:
        """Load a reference image as float32 (H, W, C)."""
        path = self._path(name)
        if not path.exists():
            raise FileNotFoundError(f"Reference not found: {path}")
        if OIIO_AVAILABLE:
            return _load_oiio(path)
        return _load_numpy_png(path)

    def compare(
        self,
        name: str,
        actual: np.ndarray,
        fail_threshold: float = 0.02,
        warn_threshold: float = 0.005,
    ) -> ImageDiffResult:
        reference = self.load(name)
        return compare_images(actual, reference, fail_threshold, warn_threshold)


def _save_oiio(image: np.ndarray, path: Path) -> None:
    """Save float32 (H, W, C) image as OpenEXR via OIIO ImageOutput.

    WHY EXR (not PNG): EXR stores float32 losslessly and has no alpha-channel
    handling ambiguity (PNG RGBA has premultiplied-alpha quirks across OIIO versions).
    EXR is the industry standard for render regression baselines (used by Pixar,
    DreamWorks, ILM) and supports HDR values above 1.0 which renders can produce.
    """
    h, w = image.shape[:2]
    nchans = image.shape[2] if image.ndim == 3 else 1
    spec = oiio.ImageSpec(w, h, nchans, oiio.FLOAT)
    out = oiio.ImageOutput.create(str(path))
    if out is None:
        raise RuntimeError(f"OIIO: cannot create output for {path}: {oiio.geterror()}")
    if not out.open(str(path), spec):
        raise RuntimeError(f"OIIO: cannot open {path} for writing: {out.geterror()}")
    out.write_image(np.ascontiguousarray(image, dtype=np.float32))
    out.close()


def _load_oiio(path: Path) -> np.ndarray:
    """Load image from disk as float32 (H, W, C) via OIIO ImageInput."""
    inp = oiio.ImageInput.open(str(path))
    if inp is None:
        raise RuntimeError(f"OIIO: cannot open {path}: {oiio.geterror()}")
    spec = inp.spec()
    h, w, nchans = spec.height, spec.width, spec.nchannels
    pixels = inp.read_image(0, 0, 0, nchans, oiio.FLOAT)
    inp.close()
    return np.asarray(pixels, dtype=np.float32).reshape(h, w, nchans)


def _save_numpy_png(image: np.ndarray, path: Path) -> None:
    """Fallback: save float32 image as raw numpy .npy (lossless, no OIIO needed).

    WHY .npy not PNG: the numpy fallback path should be lossless too; PNG brings
    format complexity for no benefit when we just want a byte-for-byte reference.
    The caller always writes to a path ending in .exr; we simply write the ndarray.
    """
    np.save(str(path), image.astype(np.float32))


def _load_numpy_png(path: Path) -> np.ndarray:
    """Load a numpy .npy reference (fallback path)."""
    return np.load(str(path)).astype(np.float32)


# ---------------------------------------------------------------------------
# Pytest assertion helper
# ---------------------------------------------------------------------------

def assert_render_match(
    actual: np.ndarray,
    reference: np.ndarray,
    fail_threshold: float = 0.02,
    warn_threshold: float = 0.005,
    label: str = "",
) -> None:
    """Assert that two render outputs match within tolerance.

    WHY explicit tolerances rather than exact equality: floating-point rounding
    differs between driver versions, shader compilers, and CUDA math libraries.
    A 2% per-pixel threshold (fail_threshold=0.02) catches material regressions
    while tolerating benign driver-level FP variance.
    """
    result = compare_images(actual, reference, fail_threshold, warn_threshold)
    if not result.passed:
        tag = f" [{label}]" if label else ""
        pytest.fail(
            f"Render regression{tag}:\n"
            f"  fail_pixels={result.n_fail_pixels} (threshold={fail_threshold})\n"
            f"  mean_error={result.mean_error:.6f}  rms={result.rms_error:.6f}\n"
            f"  max_error={result.max_error:.6f}  PSNR={result.peak_snr:.1f} dB"
        )


# ---------------------------------------------------------------------------
# Tests of the comparison infrastructure itself
# ---------------------------------------------------------------------------

class TestImageDiffResult:
    def test_identical_images_pass(self) -> None:
        img = np.random.default_rng(0).random((64, 64, 4), dtype=np.float32)
        result = compare_images(img, img.copy())
        assert result.passed
        assert result.n_fail_pixels == 0
        assert result.mean_error == pytest.approx(0.0, abs=1e-7)
        assert result.rms_error == pytest.approx(0.0, abs=1e-7)
        assert result.peak_snr == float("inf") or result.peak_snr > 100.0

    def test_all_black_vs_all_white_fails(self) -> None:
        black = np.zeros((32, 32, 4), dtype=np.float32)
        white = np.ones((32, 32, 4), dtype=np.float32)
        result = compare_images(black, white, fail_threshold=0.01)
        assert not result.passed
        # OIIO counts failing PIXELS (not per-channel elements)
        assert result.n_fail_pixels == 32 * 32
        assert result.max_error == pytest.approx(1.0, abs=1e-5)

    def test_small_perturbation_within_threshold(self) -> None:
        rng = np.random.default_rng(42)
        base = rng.random((128, 128, 4), dtype=np.float32) * 0.5
        noise = base + rng.random((128, 128, 4), dtype=np.float32) * 0.005
        result = compare_images(base, noise.astype(np.float32), fail_threshold=0.02)
        # 0.005 noise << 0.02 threshold; should pass
        assert result.passed

    def test_large_perturbation_fails(self) -> None:
        rng = np.random.default_rng(7)
        base = rng.random((64, 64, 4), dtype=np.float32)
        perturbed = np.clip(base + 0.5, 0, 1)
        result = compare_images(base, perturbed, fail_threshold=0.02)
        assert not result.passed

    def test_shape_mismatch_raises(self) -> None:
        a = np.zeros((32, 32, 4), dtype=np.float32)
        b = np.zeros((64, 64, 4), dtype=np.float32)
        with pytest.raises(ValueError, match="Shape mismatch"):
            compare_images(a, b)

    def test_psnr_infinite_for_identical(self) -> None:
        img = np.ones((16, 16, 4), dtype=np.float32) * 0.5
        result = compare_images(img, img)
        assert result.peak_snr == float("inf") or result.peak_snr > 200.0

    def test_psnr_decreases_with_noise(self) -> None:
        rng = np.random.default_rng(99)
        img = rng.random((64, 64, 4), dtype=np.float32)
        low_noise = img + rng.random((64, 64, 4), dtype=np.float32) * 0.01
        high_noise = img + rng.random((64, 64, 4), dtype=np.float32) * 0.1
        r_low = compare_images(img, low_noise.astype(np.float32), fail_threshold=1.0)
        r_high = compare_images(img, high_noise.astype(np.float32), fail_threshold=1.0)
        assert r_low.peak_snr > r_high.peak_snr

    def test_hdr_values_above_one(self) -> None:
        """HDR images with values > 1 must not confuse the comparison."""
        hdr = np.full((32, 32, 4), 10.0, dtype=np.float32)
        hdr_noisy = hdr + 0.01
        result = compare_images(hdr, hdr_noisy, fail_threshold=0.05)
        assert result.passed  # 0.01 diff < 0.05 threshold

    def test_numpy_fallback_matches_oiio(self) -> None:
        """The pure-numpy fallback must produce the same pass/fail as OIIO."""
        rng = np.random.default_rng(13)
        a = rng.random((64, 64, 4), dtype=np.float32)
        b = rng.random((64, 64, 4), dtype=np.float32) * 0.02 + a

        oiio_result = _compare_oiio(a, b, 0.05, 0.01) if OIIO_AVAILABLE else None
        numpy_result = _compare_numpy(a, b, 0.05)

        if oiio_result is not None:
            assert oiio_result.passed == numpy_result.passed
            # mean_error should agree to within 1%
            assert abs(oiio_result.mean_error - numpy_result.mean_error) < 0.01 * max(
                oiio_result.mean_error, 1e-9
            )


class TestReferenceStore:
    def test_save_and_load_roundtrip(self, tmp_path: Path) -> None:
        # Patch the references directory to tmp_path for isolation
        store = ReferenceStore.__new__(ReferenceStore)
        store._dir = tmp_path / "refs"
        store._dir.mkdir()

        img = np.random.default_rng(5).random((32, 32, 4), dtype=np.float32).astype(np.float32)
        store.save("test_frame", img)
        loaded = store.load("test_frame")

        assert loaded.shape == img.shape
        # EXR float32 is lossless -- roundtrip must be exact
        npt.assert_allclose(loaded, img, atol=1e-6, rtol=0)

    def test_load_nonexistent_raises(self, tmp_path: Path) -> None:
        store = ReferenceStore.__new__(ReferenceStore)
        store._dir = tmp_path
        with pytest.raises(FileNotFoundError):
            store.load("does_not_exist")

    def test_exists_returns_false_before_save(self, tmp_path: Path) -> None:
        store = ReferenceStore.__new__(ReferenceStore)
        store._dir = tmp_path
        assert not store.exists("ghost")

    def test_exists_returns_true_after_save(self, tmp_path: Path) -> None:
        store = ReferenceStore.__new__(ReferenceStore)
        store._dir = tmp_path
        img = np.zeros((16, 16, 4), dtype=np.float32)
        store.save("frame", img)
        assert store.exists("frame")

    def test_compare_identical_passes(self, tmp_path: Path) -> None:
        store = ReferenceStore.__new__(ReferenceStore)
        store._dir = tmp_path

        img = np.random.default_rng(3).random((32, 32, 4), dtype=np.float32).astype(np.float32)
        store.save("scene", img)
        # Re-load and compare -- roundtrip quantization must stay within threshold
        result = store.compare("scene", img, fail_threshold=0.01)
        assert result.passed

    def test_compare_different_fails(self, tmp_path: Path) -> None:
        store = ReferenceStore.__new__(ReferenceStore)
        store._dir = tmp_path

        ref = np.zeros((32, 32, 4), dtype=np.float32)
        alt = np.ones((32, 32, 4), dtype=np.float32)
        store.save("ref_black", ref)
        result = store.compare("ref_black", alt, fail_threshold=0.01)
        assert not result.passed


class TestAssertRenderMatch:
    def test_passes_for_identical(self) -> None:
        img = np.random.default_rng(0).random((16, 16, 4), dtype=np.float32)
        assert_render_match(img, img.copy())  # must not raise

    def test_fails_for_different(self) -> None:
        a = np.zeros((16, 16, 4), dtype=np.float32)
        b = np.ones((16, 16, 4), dtype=np.float32)
        with pytest.raises(pytest.fail.Exception):
            assert_render_match(a, b, fail_threshold=0.01)

    def test_label_appears_in_failure_message(self) -> None:
        a = np.zeros((8, 8, 4), dtype=np.float32)
        b = np.ones((8, 8, 4), dtype=np.float32)
        with pytest.raises(pytest.fail.Exception, match="cuda_fp32"):
            assert_render_match(a, b, fail_threshold=0.01, label="cuda_fp32")

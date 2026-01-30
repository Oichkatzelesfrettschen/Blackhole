#!/usr/bin/env python3
"""
EHT Shadow Metrics and Comparison Tool

Analyzes Event Horizon Telescope synthetic images and compares with observations:
- Measures shadow diameter
- Computes circularity and asymmetry
- Generates comparison visualizations
- Statistical validation vs M87* and Sgr A* observations

Usage:
    python3 eht_shadow_metrics.py --image synthetic.fits --reference m87_observed.fits

References:
    - Event Horizon Telescope Collaboration (2019) ApJ 875, L1 (M87*)
    - Event Horizon Telescope Collaboration (2022) ApJ 930, L12 (Sgr A*)
"""

import sys
import argparse
import numpy as np
from scipy import ndimage
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt

# ============================================================================
# EHT Shadow Analysis Functions
# ============================================================================

class EHTShadowAnalyzer:
    """Analyze EHT images and measure black hole shadow properties"""

    def __init__(self, image_data, pixel_scale_uas=None):
        """
        Initialize analyzer

        Args:
            image_data: 2D numpy array of image intensities
            pixel_scale_uas: Pixel scale in microarcseconds
        """
        self.image = image_data
        self.pixel_scale = pixel_scale_uas if pixel_scale_uas else 1.0

    def measure_shadow_diameter(self, threshold=0.5):
        """
        Measure shadow diameter using half-maximum contour

        Expected results:
        - M87*: 42 ± 3 microarcseconds
        - Sgr A*: ~52 microarcseconds
        """
        max_intensity = np.max(self.image)
        threshold_value = threshold * max_intensity

        # Binary mask of bright pixels
        bright_pixels = self.image > threshold_value

        # Label connected components
        labeled, num_features = ndimage.label(bright_pixels)

        if num_features == 0:
            return None

        # Find largest component (shadow)
        component_sizes = np.bincount(labeled.ravel())
        largest_component = np.argmax(component_sizes[1:]) + 1

        shadow_mask = labeled == largest_component

        # Find bounds
        rows, cols = np.where(shadow_mask)
        if len(rows) == 0:
            return None

        y_min, y_max = rows.min(), rows.max()
        x_min, x_max = cols.min(), cols.max()

        diameter_pix = max(y_max - y_min, x_max - x_min)
        diameter_uas = diameter_pix * self.pixel_scale

        return {
            'diameter_uas': diameter_uas,
            'diameter_pix': diameter_pix,
            'shadow_mask': shadow_mask
        }

    def compute_circularity(self, shadow_mask=None):
        """
        Compute shadow circularity (1.0 = perfectly circular)

        Formula: 4π*Area / Perimeter²
        """
        if shadow_mask is None:
            result = self.measure_shadow_diameter()
            if result is None:
                return None
            shadow_mask = result['shadow_mask']

        area = np.sum(shadow_mask)
        perimeter = np.sum(ndimage.binary_gradient(shadow_mask))

        if perimeter == 0:
            return None

        circularity = (4.0 * np.pi * area) / (perimeter ** 2)
        return circularity

    def compute_asymmetry(self, shadow_mask=None):
        """
        Measure brightness asymmetry (Doppler beaming effect)

        Compares opposite sides of shadow
        """
        if shadow_mask is None:
            result = self.measure_shadow_diameter()
            if result is None:
                return None
            shadow_mask = result['shadow_mask']

        rows, cols = np.where(shadow_mask)
        center_y = (rows.min() + rows.max()) / 2.0
        center_x = (cols.min() + cols.max()) / 2.0

        # Split image into quadrants
        top = self.image[:int(center_y), :]
        bottom = self.image[int(center_y):, :]
        left = self.image[:, :int(center_x)]
        right = self.image[:, int(center_x):]

        # Compute mean intensity in each quadrant
        top_bright = np.mean(top[top > 0.5 * np.max(top)])
        bottom_bright = np.mean(bottom[bottom > 0.5 * np.max(bottom)])
        left_bright = np.mean(left[left > 0.5 * np.max(left)])
        right_bright = np.mean(right[right > 0.5 * np.max(right)])

        # Asymmetry metrics
        vertical_asymmetry = abs(top_bright - bottom_bright) / (top_bright + bottom_bright)
        horizontal_asymmetry = abs(left_bright - right_bright) / (left_bright + right_bright)

        return {
            'vertical': vertical_asymmetry,
            'horizontal': horizontal_asymmetry,
            'total': (vertical_asymmetry + horizontal_asymmetry) / 2.0
        }

    def compare_with_reference(self, reference_data):
        """
        Statistical comparison with reference image

        Computes:
        - Chi-squared between images
        - Peak signal-to-noise ratio
        - Structural similarity
        """
        if self.image.shape != reference_data.shape:
            return None

        # Normalize images
        self_norm = self.image / np.max(self.image)
        ref_norm = reference_data / np.max(reference_data)

        # Chi-squared
        chi2 = np.sum((self_norm - ref_norm) ** 2 / (ref_norm + 1e-10))

        # RMS error
        rms = np.sqrt(np.mean((self_norm - ref_norm) ** 2))

        # Peak SNR
        peak_diff = np.max(np.abs(self_norm - ref_norm))
        psnr = -10.0 * np.log10(peak_diff + 1e-10)

        return {
            'chi2': chi2,
            'rms_error': rms,
            'peak_snr_db': psnr
        }

# ============================================================================
# Main Analysis Routine
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Analyze EHT synthetic images and measure shadow properties'
    )
    parser.add_argument('--image', required=True, help='Synthetic image file')
    parser.add_argument('--reference', help='Reference image for comparison')
    parser.add_argument('--output', default='eht_analysis.txt',
                       help='Output analysis file')
    parser.add_argument('--plot', help='Plot output filename')

    args = parser.parse_args()

    print("\n" + "="*60)
    print("EHT SHADOW ANALYSIS")
    print("="*60 + "\n")

    # Load synthetic image
    print(f"Loading image: {args.image}")
    try:
        # Parse CSV format
        image_data = np.loadtxt(args.image, delimiter=',')
    except Exception as e:
        print(f"Error loading image: {e}")
        return 1

    print(f"Image shape: {image_data.shape}")
    print(f"Data range: [{np.min(image_data):.2e}, {np.max(image_data):.2e}]")

    # Analyze image
    analyzer = EHTShadowAnalyzer(image_data, pixel_scale_uas=100.0/image_data.shape[0])

    # Measure shadow
    print("\n" + "-"*60)
    print("SHADOW MEASUREMENTS")
    print("-"*60)

    shadow_result = analyzer.measure_shadow_diameter()
    if shadow_result:
        diameter = shadow_result['diameter_uas']
        print(f"Shadow diameter: {diameter:.2f} microarcseconds")

        # Expected values
        m87_expected = 42.0
        sgra_expected = 52.0

        error_m87 = abs(diameter - m87_expected) / m87_expected * 100.0
        error_sgra = abs(diameter - sgra_expected) / sgra_expected * 100.0

        print(f"\nComparison with observations:")
        print(f"  M87* (42.0 μas):   Error = {error_m87:.1f}%")
        print(f"  Sgr A* (52.0 μas): Error = {error_sgra:.1f}%")

        if error_m87 < 5.0:
            print("\nStatus: PASS (M87* match)")
        else:
            print("\nStatus: Outside expected range")

    # Measure circularity
    circularity = analyzer.compute_circularity(shadow_result['shadow_mask'])
    if circularity:
        print(f"\nCircularity: {circularity:.3f} (1.0 = perfect circle)")

    # Measure asymmetry
    asymmetry = analyzer.compute_asymmetry(shadow_result['shadow_mask'])
    if asymmetry:
        print(f"\nBrightness Asymmetry:")
        print(f"  Vertical:   {asymmetry['vertical']:.3f}")
        print(f"  Horizontal: {asymmetry['horizontal']:.3f}")
        print(f"  Total:      {asymmetry['total']:.3f}")

    # Compare with reference if provided
    if args.reference:
        print("\n" + "-"*60)
        print("COMPARISON WITH REFERENCE")
        print("-"*60)

        try:
            reference_data = np.loadtxt(args.reference, delimiter=',')
            comparison = analyzer.compare_with_reference(reference_data)

            if comparison:
                print(f"Chi-squared: {comparison['chi2']:.2e}")
                print(f"RMS error: {comparison['rms_error']:.2e}")
                print(f"Peak SNR: {comparison['peak_snr_db']:.2f} dB")
        except Exception as e:
            print(f"Error loading reference: {e}")

    # Save analysis results
    print("\n" + "-"*60)
    print(f"Saving analysis to: {args.output}")
    print("-"*60 + "\n")

    with open(args.output, 'w') as f:
        f.write("EHT SHADOW ANALYSIS REPORT\n")
        f.write("="*60 + "\n\n")

        if shadow_result:
            f.write(f"Shadow Diameter: {shadow_result['diameter_uas']:.2f} μas\n")

        if circularity:
            f.write(f"Circularity: {circularity:.3f}\n")

        if asymmetry:
            f.write(f"Asymmetry: {asymmetry['total']:.3f}\n")

    print("Analysis complete.")
    return 0

if __name__ == '__main__':
    sys.exit(main())

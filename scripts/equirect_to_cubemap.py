#!/usr/bin/env python3
"""Convert an equirectangular panorama to six cubemap face images.

Usage:
    python3 scripts/equirect_to_cubemap.py INPUT OUTPUT_DIR [--face-size N]

Reads an equirectangular image (2:1 aspect ratio) and writes six PNG face
images into OUTPUT_DIR: right.png, left.png, top.png, bottom.png, front.png,
back.png.  The face naming convention matches the OpenGL cubemap face order
used by loadCubemap() in src/texture.cpp.

Optionally generates a matching flat 2D background crop (--flat-crop) by
extracting the front-facing hemisphere as a 2:1.5 image.
"""

import argparse
import math
import sys
from pathlib import Path

import numpy as np
from PIL import Image


# OpenGL cubemap face directions: (forward, up, right) in world space.
# World: +X = right, +Y = up, +Z = backward (into screen).
FACE_DIRS = {
    "right":  (np.array([ 1, 0, 0]), np.array([0, 1, 0]), np.array([0, 0,  1])),
    "left":   (np.array([-1, 0, 0]), np.array([0, 1, 0]), np.array([0, 0, -1])),
    "top":    (np.array([0,  1, 0]), np.array([0, 0, 1]), np.array([1, 0,  0])),
    "bottom": (np.array([0, -1, 0]), np.array([0, 0,-1]), np.array([1, 0,  0])),
    "front":  (np.array([0, 0, -1]), np.array([0, 1, 0]), np.array([1, 0,  0])),
    "back":   (np.array([0, 0,  1]), np.array([0, 1, 0]), np.array([-1,0,  0])),
}


def equirect_to_face(equirect: np.ndarray, face_name: str, face_size: int) -> np.ndarray:
    """Render one cubemap face from an equirectangular source.

    For each pixel in the output face, compute the 3D direction vector,
    convert to spherical coordinates, then sample the equirectangular image
    using bilinear interpolation.
    """
    h_eq, w_eq = equirect.shape[:2]
    forward, up, right = FACE_DIRS[face_name]

    # Normalized device coordinates for each pixel in the face.
    u = np.linspace(-1, 1, face_size, dtype=np.float64)
    v = np.linspace(-1, 1, face_size, dtype=np.float64)
    uu, vv = np.meshgrid(u, v)

    # 3D direction for each pixel: forward + uu * right + (-vv) * up
    dirs = (forward[np.newaxis, np.newaxis, :]
            + uu[:, :, np.newaxis] * right[np.newaxis, np.newaxis, :]
            + (-vv)[:, :, np.newaxis] * up[np.newaxis, np.newaxis, :])

    # Normalize direction vectors.
    norms = np.linalg.norm(dirs, axis=2, keepdims=True)
    dirs = dirs / norms

    # Convert to spherical: theta (elevation), phi (azimuth).
    x, y, z = dirs[:, :, 0], dirs[:, :, 1], dirs[:, :, 2]
    theta = np.arcsin(np.clip(y, -1, 1))       # [-pi/2, pi/2]
    phi = np.arctan2(x, -z)                     # [-pi, pi]

    # Map to equirectangular pixel coordinates.
    eq_x = (phi / (2 * math.pi) + 0.5) * (w_eq - 1)
    eq_y = (0.5 - theta / math.pi) * (h_eq - 1)

    # Bilinear interpolation indices.
    x0 = np.floor(eq_x).astype(np.int32)
    y0 = np.floor(eq_y).astype(np.int32)
    x1 = np.clip(x0 + 1, 0, w_eq - 1)
    y1 = np.clip(y0 + 1, 0, h_eq - 1)
    x0 = np.clip(x0, 0, w_eq - 1)
    y0 = np.clip(y0, 0, h_eq - 1)

    # Wrap x coordinates for seamless horizontal tiling.
    x0 = x0 % w_eq
    x1 = x1 % w_eq

    fx = (eq_x - np.floor(eq_x)).astype(np.float32)
    fy = (eq_y - np.floor(eq_y)).astype(np.float32)

    # Sample four corners.
    c00 = equirect[y0, x0].astype(np.float32)
    c10 = equirect[y0, x1].astype(np.float32)
    c01 = equirect[y1, x0].astype(np.float32)
    c11 = equirect[y1, x1].astype(np.float32)

    fx = fx[:, :, np.newaxis]
    fy = fy[:, :, np.newaxis]

    result = (c00 * (1 - fx) * (1 - fy)
              + c10 * fx * (1 - fy)
              + c01 * (1 - fx) * fy
              + c11 * fx * fy)

    return np.clip(result, 0, 255).astype(np.uint8)


def extract_flat_crop(equirect: np.ndarray, out_w: int, out_h: int) -> np.ndarray:
    """Extract a front-facing flat crop from the equirectangular image.

    Takes the central portion of the equirectangular image, spanning
    roughly the front hemisphere, and resizes to out_w x out_h.
    """
    h_eq, w_eq = equirect.shape[:2]
    # Take center 50% horizontally (front hemisphere), full vertical.
    x_start = w_eq // 4
    x_end = 3 * w_eq // 4
    crop = equirect[:, x_start:x_end]
    img = Image.fromarray(crop)
    img = img.resize((out_w, out_h), Image.LANCZOS)
    return np.array(img)


def main():
    parser = argparse.ArgumentParser(description="Convert equirectangular panorama to cubemap faces")
    parser.add_argument("input", help="Input equirectangular image (2:1 ratio)")
    parser.add_argument("output_dir", help="Output directory for cubemap face PNGs")
    parser.add_argument("--face-size", type=int, default=2048,
                        help="Pixel size of each cubemap face (default: 2048)")
    parser.add_argument("--flat-crop", action="store_true",
                        help="Also generate a flat 2D background crop")
    parser.add_argument("--flat-width", type=int, default=2048,
                        help="Width of flat crop output (default: 2048)")
    parser.add_argument("--flat-height", type=int, default=1536,
                        help="Height of flat crop output (default: 1536)")
    parser.add_argument("--flat-name", type=str, default="flat_2k.jpg",
                        help="Filename for flat crop output (default: flat_2k.jpg)")
    args = parser.parse_args()

    input_path = Path(args.input)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Loading {input_path}...")
    img = Image.open(input_path).convert("RGB")
    equirect = np.array(img)
    h, w = equirect.shape[:2]
    print(f"  Source: {w}x{h} (aspect {w/h:.2f}:1)")

    if abs(w / h - 2.0) > 0.1:
        print(f"  WARNING: aspect ratio {w/h:.2f} deviates from 2:1 equirectangular standard")

    face_names = ["right", "left", "top", "bottom", "front", "back"]
    for name in face_names:
        print(f"  Rendering {name}...")
        face = equirect_to_face(equirect, name, args.face_size)
        out_path = output_dir / f"{name}.png"
        Image.fromarray(face).save(out_path, "PNG")
        print(f"    Saved {out_path} ({args.face_size}x{args.face_size})")

    if args.flat_crop:
        print(f"  Extracting flat crop...")
        flat = extract_flat_crop(equirect, args.flat_width, args.flat_height)
        flat_path = output_dir / args.flat_name
        Image.fromarray(flat).save(flat_path, quality=92)
        print(f"    Saved {flat_path} ({args.flat_width}x{args.flat_height})")

    print("Done.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Create a cubemap skybox from a flat 2D image.

Projects the flat image onto the front face of the cubemap and fills
the remaining five faces with corresponding regions from a reference
equirectangular panorama (defaulting to the NASA Deep Star Map).

Usage:
    python3 scripts/flat_to_cubemap.py INPUT OUTPUT_DIR [--reference EQUIRECT]
"""

import argparse
import sys
from pathlib import Path

import numpy as np
from PIL import Image

# Reuse the equirect_to_face function from the main conversion tool.
sys.path.insert(0, str(Path(__file__).parent))
from equirect_to_cubemap import equirect_to_face


def main():
    parser = argparse.ArgumentParser(
        description="Create cubemap from flat image + reference starfield")
    parser.add_argument("input", help="Input flat 2D image (used for front face)")
    parser.add_argument("output_dir", help="Output directory for cubemap faces")
    parser.add_argument("--reference",
                        default="assets/backgrounds/equirect/nasa_deep_starmap_4k.jpg",
                        help="Reference equirectangular panorama for non-front faces")
    parser.add_argument("--face-size", type=int, default=2048,
                        help="Face size in pixels (default: 2048)")
    args = parser.parse_args()

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Load the flat image for the front face.
    print(f"Loading flat image: {args.input}")
    flat_img = Image.open(args.input).convert("RGB")
    flat_resized = flat_img.resize((args.face_size, args.face_size), Image.LANCZOS)
    flat_resized.save(output_dir / "front.png", "PNG")
    print(f"  front.png: flat image resized to {args.face_size}x{args.face_size}")

    # Load reference equirectangular for the other 5 faces.
    print(f"Loading reference panorama: {args.reference}")
    ref_img = Image.open(args.reference).convert("RGB")
    ref_equirect = np.array(ref_img)

    for face_name in ["right", "left", "top", "bottom", "back"]:
        print(f"  Rendering {face_name} from reference...")
        face = equirect_to_face(ref_equirect, face_name, args.face_size)
        Image.fromarray(face).save(output_dir / f"{face_name}.png", "PNG")

    print("Done.")


if __name__ == "__main__":
    main()

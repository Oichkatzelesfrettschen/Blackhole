# Blackhole Physics Remote Asset Library Setup

## Quick Local Server

Serve the asset library directory over HTTP for team access:

    cd /home/eirikr/Github/Blackhole/blender_addon/blackhole_physics/asset_library
    python3 -m http.server 8080

Then in Blender on other machines:
1. Edit > Preferences > File Paths > Asset Libraries
2. Add Remote Library: http://<your-ip>:8080/

## Contents

- blackhole_physics_bundle.blend: Full scene with all BH objects, materials, textures
- blender_assets.cats.txt: Asset catalog definitions

## Bundle includes

- Event horizon mesh (Kerr oblate, a*=0.9375)
- Ergosphere mesh
- Accretion disk (8192 verts, Novikov-Thorne temperature)
- 64 photon geodesic curves
- Lensing map (1024x1024, redshift + Doppler)
- Disk emission texture (1024x256, blackbody)
- Materials: emission disk, black horizon, glass ergosphere, emissive geodesics
- BH_TemperatureToColor shader node group
- M87* and Sgr A* parameter presets

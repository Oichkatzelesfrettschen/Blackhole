# Background asset provenance audit

The renderer draws its sky backdrops from `assets/backgrounds/manifest.json`,
which is the single source of truth mapping an asset id to a file, a title, and
its upstream source, license, and credit. This audit verifies that each entry's
declared identity matches the image the file actually contains, so the manifest
can be trusted as a provenance record rather than a set of hopeful labels.

## Method

Ground truth is the image's own `EXIF:ImageDescription`, written by the space
agency at publication, read back with ImageMagick:

```
identify -format "%[EXIF:ImageDescription]" <file>
```

Each entry's declared title is compared against that description (and, where the
description is empty, against the credit line and the upstream image code). The
audit is reproducible from `scripts/audit_asset_provenance.py`, which walks the
manifest and prints every asset's declared title beside its verified content.

## Findings

Five entries declared an object different from the one their file contained. The
descriptions and credits identify the true content unambiguously.

| Declared id / title | File contained | Evidence |
| --- | --- | --- |
| `jwst_tarantula_nebula` -- Tarantula Nebula | Cartwheel galaxy | EXIF: "the Cartwheel and its companion galaxies"; duplicate of `jwst_cartwheel_galaxy` |
| `jwst_stephans_quintet` -- Stephan's Quintet | Cosmic Cliffs (Carina) | EXIF matches `jwst_carina_cosmic_cliffs` verbatim; duplicate |
| `jwst_orion_bar` -- Orion Bar | Comet 238P/Read | EXIF: "artist's concept of Comet 238P/Read sublimating its water ice" |
| `esa_heic1402a_4k` -- Horsehead Nebula | Tarantula Nebula (Hubble IR) | EXIF: "the Tarantula Nebula in infrared light"; credit E. Sabbi produced the 30 Doradus mosaic |
| `esa_heic1402a_large` -- Horsehead Nebula | Tarantula Nebula (Hubble IR) | same as above |

Two further entries carried uninformative titles (the bare NASA/JPL image code);
their content was verified and named.

| Declared id | Content verified | Now titled |
| --- | --- | --- |
| `nasa_pia15416` | GALEX ultraviolet field | GALEX Ultraviolet Field (PIA15416) |
| `nasa_pia08506` | Andromeda galaxy, visible light | Andromeda Galaxy (M31, PIA08506) |

The remaining entries verified correct: Carina, Crab, SMACS 0723 deep field,
Pillars of Creation, Southern Ring, Cartwheel, Jupiter auroras, Cygnus Loop
(`nasa_pia15415`), and Westerlund 2 (`esa_heic1509a`).

## Corrections applied

- `jwst_tarantula_nebula` and `jwst_stephans_quintet` were removed: their files
  (`tarantula-nebula-2k.jpg`, `stephans-quintet-2k.jpg`) duplicated the
  correctly labelled Cartwheel and Carina entries and were deleted. The renderer
  keeps a genuine Tarantula through the relabelled `esa_heic1402a` entries.
- `jwst_orion_bar` became `jwst_comet_238p_read`; its file was renamed
  `orion-bar-2k.jpg` -> `comet-238p-read-2k.jpg`.
- Both `esa_heic1402a` entries are retitled Tarantula Nebula (Hubble infrared),
  matching their content and the E. Sabbi credit.
- `nasa_pia15416` and `nasa_pia08506` gained descriptive titles.
- Every corrected entry records a `verifiedContent` field quoting the EXIF
  evidence, so a future reader can confirm the identity without re-running the
  audit.

The campaign backdrop picker was corrected separately: it now offers only
verified backdrops (Cosmic Cliffs, Crab, Southern Ring, Cartwheel) and no longer
loads the mislabelled files.

## Known remaining debt

- **Duplicate copies under `assets/backgrounds/jwst/`.** The same JWST images are
  vendored in both `source/` and `jwst/`; the manifest references only `source/`,
  so the `jwst/` copies (including the now-removed mislabelled names) are
  unreferenced duplicates and are candidates for removal.
- **Orphaned skyboxes.** `assets/skybox_jwst_tarantula/` and
  `assets/skybox_jwst_stephans_quintet/` were generated from the mislabelled
  source images and are no longer referenced by any manifest entry.
- **`jwst_wolf_rayet_124`.** Its description reads as an artist's illustration
  rather than the NIRCam/MIRI photograph; the title is left as published pending
  a source check.
- **Git-LFS budget.** The upstream account's LFS budget blocks new pushes;
  downloads still work. The runtime-critical defaults (the default background and
  the campaign picker sources) ship as ordinary git blobs so a fresh clone works
  without a git-lfs fetch. The large archive originals remain in LFS.

## Re-running the audit

```
python3 scripts/audit_asset_provenance.py
```

Any future asset should be added to the manifest with its `verifiedContent`
recorded at the same time, so the provenance record never drifts from the files
again.

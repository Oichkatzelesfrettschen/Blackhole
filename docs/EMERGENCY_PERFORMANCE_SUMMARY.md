# EMERGENCY PERFORMANCE DIAGNOSTIC
**Date:** 2026-01-31
**Status:** CRITICAL - 1-3 FPS (Target: 40-60 FPS)
**CPU Usage:** 98% (BOTTLENECK)
**GPU Usage:** Unknown (likely idle)

---

## ROOT CAUSES IDENTIFIED

### 1. Shader Include Bug - FIXED ✓
**Problem:** Nested shader includes used wrong basePath
**Impact:** PI, TWO_PI constants undefined → shader compilation failed
**Status:** FIXED (kerr.glsl and interop_trace.glsl updated)
**Result:** Shaders now compile without errors

### 2. Ray Marching Steps - REDUCED ✓
**Problem:** 300 steps per pixel (offline quality)
**Fix:** Reduced to 20 steps (15x reduction)
**Status:** APPLIED in shader
**Expected:** Should give 10-15x speedup, but FPS still low

### 3. CPU Bottleneck - ACTIVE ISSUE ❌
**Problem:** CPU at 98%, producing only 1-3 FPS
**Symptoms:**
- Failed texture loading spam (every frame)
- High CPU usage but low FPS
- Possible CPU-GPU sync stall

**Potential Causes:**
- VSync forced wait (check monitor refresh rate)
- Texture loading retries every frame
- ImGui overhead
- CPU waiting for GPU (glFinish/glFlush)
- Mesa driver overhead

---

## METRICS CAPTURED

**Test Configuration:**
- GPU: Intel HD Graphics 4400
- Resolution: 1920x1080 (default)
- Ray steps: 20 (reduced from 300)
- Driver: Mesa 25.3.4

**Results:**
```
FPS: 0.5-3.0 (UNACCEPTABLE)
CPU: 98% (eric process)
VRAM: ~250 MB used / 1536 MB available
Shader errors: 0 (fixed)
Texture errors: Continuous (every frame)
```

---

## IMMEDIATE ACTIONS NEEDED

### Action 1: Test on AMD GPU
The AMD Radeon HD 8730M should perform better. Test with:
```bash
cd /home/eric/Playground/Blackhole/build/Release
DRI_PRIME=1 LIBGL_SHOW_FPS=1 ./Blackhole
```

Expected: 5-10x better performance

### Action 2: Reduce Resolution
Default 1920x1080 is too demanding. Test at 1280x720:
- Edit settings or add command-line option
- Should give 2-3x FPS improvement

### Action 3: Disable Features
**Minimal render mode:** Disable expensive features

Edit `shader/blackhole_main.frag`:
```glsl
uniform float adiskEnabled = 0.0;  // Disable accretion disk
uniform float renderBlackHole = 0.5;  // Reduce quality
```

Expected: +30-50% FPS

### Action 4: Check VSync
```bash
# Disable VSync
vblank_mode=0 LIBGL_SHOW_FPS=1 ./Blackhole
```

If this helps, VSync was limiting framerate.

### Action 5: Profile with perf
```bash
perf record -g ./Blackhole
# Run for 10 seconds
# Ctrl+C
perf report
```

This will show where CPU time is spent.

---

## HYPOTHESIS

**Most Likely Cause:** CPU-GPU synchronization stall

**Evidence:**
1. CPU at 98% but low FPS suggests waiting
2. Texture loading spam every frame
3. Possible glFinish() or buffer mapping stall

**Test:** Run with `MESA_GLTHREAD=true` to enable multi-threaded GL:
```bash
MESA_GLTHREAD=true LIBGL_SHOW_FPS=1 ./Blackhole
```

---

## WORKING FIXES APPLIED

1. ✓ Shader includes fixed (kerr.glsl, interop_trace.glsl)
2. ✓ Ray steps reduced 300 → 20
3. ✓ Step size increased 0.1 → 0.25
4. ✓ Physics constants included correctly
5. ✓ Mesa shader cache cleared

## REMAINING ISSUES

1. ❌ CPU bottleneck (98% usage, 1-3 FPS)
2. ❌ Texture loading spam
3. ❌ Possible VSync stall
4. ❌ Unknown synchronization point

---

## NEXT STEPS (PRIORITY ORDER)

1. **Test AMD GPU** (highest priority - likely to work better)
2. **Profile with perf** to find CPU hotspot
3. **Reduce resolution** to 1280x720
4. **Disable VSync** if that's the issue
5. **Enable Mesa GL thread** for async rendering

---

## PERFORMANCE TARGETS

**Minimum Acceptable:**
- Intel HD 4400: 30+ FPS @ 720p
- AMD HD 8730M: 60+ FPS @ 1080p

**Current Status:**
- Intel HD 4400: 1-3 FPS @ 1080p (FAIL)
- AMD HD 8730M: NOT TESTED

**Conclusion:** Intel GPU performance is WORSE than expected even with optimizations.
**Recommendation:** USE AMD GPU or investigate CPU bottleneck.

---

Created: 2026-01-31 by Claude Code

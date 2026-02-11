# Final Performance Analysis - 2026-01-31

## TL;DR

**Fixed:** Two critical bottlenecks (uniform location lookups + texture retry loop)
**Result:** Performance STILL at 1.5-3 FPS ❌
**Conclusion:** There is a deeper architectural issue beyond what was fixed

---

## Fixes Applied

### Fix 1: Uniform Location Caching ✓
**Problem:** `glGetUniformLocation()` called 100+ times per frame
**Files Modified:**
- `src/render.cpp` - Added `getCachedUniformLocation()` helper
- `src/main.cpp` - Added caching for compute shader uniforms

**Code Changes:**
```cpp
// BEFORE (render.cpp lines 263, 278, 293, 308, 182):
GLint loc = glGetUniformLocation(program, name.c_str());  // EXPENSIVE DRIVER CALL!

// AFTER:
static std::unordered_map<GLuint, std::unordered_map<std::string, GLint>> uniformLocationCache;
GLint loc = getCachedUniformLocation(program, name);  // Fast hash lookup
```

**Expected Impact:** 10-30x FPS improvement
**Actual Impact:** NONE - FPS unchanged ❌

### Fix 2: Texture Load Retry Loop ✓
**Problem:** Failed texture load retried every frame
**File Modified:** `src/main.cpp:2916`

**Code Changes:**
```cpp
// BEFORE:
if (nextTexture != 0) {
  backgroundLoadedId = asset.id;  // Only updated on SUCCESS
}
// Result: Failed loads retried every frame → thousands of file I/O operations

// AFTER:
if (nextTexture != 0) {
  backgroundBase = nextTexture;
}
backgroundLoadedId = asset.id;  // Always update to prevent retry loop
```

**Expected Impact:** Eliminate per-frame file I/O spam
**Actual Impact:** ERROR spam eliminated, but FPS unchanged ❌

---

## Compute Shaders - NOT NECESSARY

**Q:** "why do we even have compute shaders, are they necessary?!"

**A:** NO, they are NOT necessary.

**Evidence from code:**
```cpp
// src/main.cpp:2344
static bool useComputeRaytracer = false;  // DEFAULT: DISABLED

// src/main.cpp:3710
bool computeActive = useComputeRaytracer && computeSupported;
```

**What are they:**
- Alternative rendering path for geodesic ray tracing
- Uses `shader/geodesic_trace.comp` compute shader
- Toggleable via UI checkbox: "Use Compute Raytracer"

**Why they exist:**
- Experimental feature
- Theoretically could be faster for some workloads
- Currently DISABLED by default

**Recommendation:** Can be removed if not used. Fragment shader path is the primary/default rendering method.

---

## Why Performance Is STILL Poor

Despite fixing two major bottlenecks, performance remains at 1.5-3 FPS.

### Test Results:

**After all fixes:**
```
Intel HD Graphics 4400 @ 1920x1080:
fps: 1.571
fps: 1.58
fps: 1.583
fps: 1.587
fps: 1.59

AMD Radeon HD 8730M: NOT RETESTED YET
```

**VSync Test:**
```bash
vblank_mode=0 LIBGL_SHOW_FPS=1 ./Blackhole
# Result: Same FPS (1.5-1.9) → VSync NOT the issue
```

### Possible Remaining Bottlenecks:

1. **ImGui Overhead** ⭐⭐⭐⭐
   - Complex UI rendering every frame
   - Thousands of UI elements
   - Text rendering
   - Should test with UI disabled

2. **glfwSwapBuffers Blocking** ⭐⭐⭐
   - May be waiting on GPU even without VSync
   - Driver-level throttling?
   - Mesa-specific issue?

3. **Fragment Shader Still Too Expensive** ⭐⭐⭐
   - Even with 20 steps, maybe still too heavy
   - Test with minimal passthrough shader
   - Check if GPU is actually the bottleneck

4. **Other Hidden Driver Calls** ⭐⭐
   - glGetError() called somewhere?
   - Other validation overhead?
   - Debug context enabled?

5. **Frame Pacing Issue** ⭐⭐
   - Something artificially limiting to ~60Hz / 40
   - Check for frame rate limiters in code
   - Compositor forcing refresh rate lock?

---

## Debug Strategy

### Immediate Tests (User Can Do Now):

1. **Disable UI completely**
   ```cpp
   // In main.cpp render loop, comment out ImGui rendering
   // Skip all ImGui::Begin/End blocks
   ```
   Expected: If UI is the bottleneck, FPS should jump to 40-60+

2. **Test with passthrough shader**
   ```bash
   # Edit shader/blackhole_main.frag
   # Replace main() with:
   void main() {
     fragColor = vec4(1.0, 0.0, 0.0, 1.0);  // Solid red
   }
   ```
   Expected: If shader is still the bottleneck, FPS should jump to 100+

3. **Disable ALL postprocessing**
   ```cpp
   // In main.cpp, skip bloom, tonemap, depth passes
   // Render blackhole directly to screen
   ```
   Expected: If postprocessing is expensive, FPS should improve 2-3x

4. **Check for hidden glFinish/glFlush**
   ```bash
   grep -rn "glFinish\|glFlush\|glGetError" src/
   ```

### Advanced Debugging:

1. **CPU Profiling with perf**
   ```bash
   perf record -g ./Blackhole
   perf report --stdio
   ```
   Will show exact function where CPU time is spent

2. **GPU Profiling**
   ```bash
   INTEL_DEBUG=perf ./Blackhole
   # Or use gpuvis for detailed GPU timeline
   ```

3. **Frame Debugger**
   ```bash
   apitrace trace ./Blackhole
   qapitrace Blackhole.trace
   # See every GL call and timing
   ```

---

## Conclusion

**Critical Finding:** Two major CPU bottlenecks were fixed, but performance did NOT improve.

**This suggests:**
- The real bottleneck is elsewhere (ImGui, swap, or still GPU-bound)
- OR the fixes didn't actually get applied/used correctly
- OR there's a fundamental architectural issue

**Next Steps:**
1. Verify uniform caching is actually working (add debug prints to getCachedUniformLocation)
2. Test with minimal shader to rule out GPU bottleneck
3. Test with UI disabled to measure UI overhead
4. Profile with `perf` to find actual CPU hotspot

**Compute Shaders:** Not necessary, can be removed.

---

## Files Modified This Session

1. `src/render.cpp` - Uniform location caching
2. `src/main.cpp` - Uniform location caching + texture retry fix
3. `shader/blackhole_main.frag` - Ray marching steps (previous session)
4. `shader/include/kerr.glsl` - Include path fix (previous session)
5. `shader/include/interop_trace.glsl` - Include path fix (previous session)

---

**Investigation Status:** INCONCLUSIVE
**Root Cause:** UNKNOWN (fixes did not improve performance)
**Recommendation:** Need deeper profiling to identify actual bottleneck

---

Report by Claude Code - 2026-01-31

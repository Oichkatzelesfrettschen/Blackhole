# Conan 2.X Migration Guide

**Status**: Scoping deprecated features and modern replacements
**Date**: 2026-02-11

## Deprecation Warnings Analysis

Current warnings from Conan install:

```
WARN: deprecated: Usage of deprecated Conan 1.X features that will be removed in Conan 2.X:
WARN: deprecated:     'cpp_info.names' used in: hdf5/1.14.6, bzip2/1.0.8, boost/1.90.0, glbinding/3.5.0, taskflow/3.10.0, cli11/2.6.0, entt/3.15.0
WARN: deprecated:     'cpp_info.build_modules' used in: xsimd/13.2.0, hdf5/1.14.6, bzip2/1.0.8
WARN: deprecated:     'env_info' used in: boost/1.90.0, bzip2/1.0.8
WARN: deprecated:     'cpp_info.filenames' used in: boost/1.90.0, opengl/system
WARN: deprecated:     'user_info' used in: boost/1.90.0
```

## Deprecated Features and Modern Replacements

### 1. cpp_info.names → set_property()

**Deprecated (Conan 1.X):**
```python
def package_info(self):
    self.cpp_info.names["cmake_find_package"] = "CustomName"
    self.cpp_info.names["cmake_find_package_multi"] = "CustomName"
```

**Modern (Conan 2.X):**
```python
def package_info(self):
    self.cpp_info.set_property("cmake_target_name", "CustomName")
    self.cpp_info.set_property("cmake_file_name", "CustomName")
    self.cpp_info.set_property("pkg_config_name", "customname")
```

**Affected Packages:**
- hdf5/1.14.6
- bzip2/1.0.8
- boost/1.90.0
- glbinding/3.5.0
- taskflow/3.10.0
- cli11/2.6.0
- entt/3.15.0

**Action Required:**
These are **upstream packages**. We don't control their recipes. However, we can:
1. Update to newer versions that use Conan 2.X syntax
2. Create custom recipes (override)
3. Wait for ConanCenter updates

### 2. cpp_info.build_modules → set_property()

**Deprecated (Conan 1.X):**
```python
def package_info(self):
    self.cpp_info.build_modules["cmake_find_package"] = [
        os.path.join("lib", "cmake", "module.cmake")
    ]
```

**Modern (Conan 2.X):**
```python
def package_info(self):
    self.cpp_info.set_property("cmake_build_modules", [
        os.path.join(self.package_folder, "lib", "cmake", "module.cmake")
    ])
```

**Affected Packages:**
- xsimd/13.2.0
- hdf5/1.14.6
- bzip2/1.0.8

**Action Required:**
These packages provide CMake build modules. Modern approach uses `cmake_build_modules` property.

### 3. env_info → VirtualBuildEnv/VirtualRunEnv

**Deprecated (Conan 1.X):**
```python
def package_info(self):
    self.env_info.PATH.append(os.path.join(self.package_folder, "bin"))
    self.env_info.LD_LIBRARY_PATH.append(os.path.join(self.package_folder, "lib"))
```

**Modern (Conan 2.X):**
```python
from conan.tools.env import Environment

def package_info(self):
    env = Environment()
    env.prepend_path("PATH", os.path.join(self.package_folder, "bin"))
    env.prepend_path("LD_LIBRARY_PATH", os.path.join(self.package_folder, "lib"))
    self.buildenv_info.compose_env(env)
```

Or use automatic environment management:
```python
def package_info(self):
    self.cpp_info.bindirs = ["bin"]  # Automatically added to PATH
    self.cpp_info.libdirs = ["lib"]  # Automatically added to LD_LIBRARY_PATH
```

**Affected Packages:**
- boost/1.90.0
- bzip2/1.0.8

**Action Required:**
Modern Conan 2.X uses `VirtualBuildEnv` and `VirtualRunEnv` generators automatically.

### 4. cpp_info.filenames → set_property()

**Deprecated (Conan 1.X):**
```python
def package_info(self):
    self.cpp_info.filenames["cmake_find_package"] = "FindCustom"
```

**Modern (Conan 2.X):**
```python
def package_info(self):
    self.cpp_info.set_property("cmake_file_name", "FindCustom")
```

**Affected Packages:**
- boost/1.90.0
- opengl/system

**Action Required:**
Use `cmake_file_name` property instead.

### 5. user_info → conf_info

**Deprecated (Conan 1.X):**
```python
def package_info(self):
    self.user_info.VAR = "value"
```

**Modern (Conan 2.X):**
```python
def package_info(self):
    self.conf_info.define("user.mypackage:var", "value")
```

**Affected Packages:**
- boost/1.90.0

**Action Required:**
Use `conf_info` for user-defined configuration values.

## Migration Strategy

### Phase 1: Update Package Versions (Immediate)

Check for newer versions of affected packages that support Conan 2.X:

```bash
conan search hdf5 -r conancenter
conan search boost -r conancenter
conan search bzip2 -r conancenter
```

**Recommended Updates:**
- boost: Check for 1.91.0+ (may have Conan 2.X support)
- hdf5: Check for 1.14.7+ or 1.16.x
- bzip2: Check for 1.0.9+

### Phase 2: Test with Updated Versions

Update conanfile.py:
```python
def requirements(self):
    # Try newer versions
    self.requires("boost/1.91.0", override=True)  # if available
    self.requires("hdf5/1.16.0", override=True)   # if available
```

### Phase 3: Custom Recipes (If Needed)

If upstream packages aren't updated, create custom recipes in `conan/recipes/`:

```
conan/recipes/
├── boost/
│   └── 1.90.0-conan2/
│       └── conanfile.py  # Updated with Conan 2.X syntax
├── hdf5/
│   └── 1.14.6-conan2/
│       └── conanfile.py
└── bzip2/
    └── 1.0.8-conan2/
        └── conanfile.py
```

Example custom recipe fixing `cpp_info.names`:
```python
from conan import ConanFile

class CustomPackageConan(ConanFile):
    name = "hdf5"
    version = "1.14.6-conan2"

    def requirements(self):
        # Reference original package
        self.requires("hdf5/1.14.6")

    def package_info(self):
        # Modern Conan 2.X syntax
        self.cpp_info.set_property("cmake_target_name", "HDF5")
        self.cpp_info.set_property("cmake_file_name", "HDF5")

        # Copy other package_info from original
        self.cpp_info.libs = ["hdf5", "hdf5_hl"]
```

### Phase 4: ConanCenter Monitoring

Track ConanCenter updates:
- https://github.com/conan-io/conan-center-index

Submit pull requests for outdated recipes if needed.

## Implementation Plan

### Immediate Actions (Low Risk)

1. **Update conanfile.py version overrides:**
   ```python
   def requirements(self):
       # Check for newer versions first
       self.requires("boost/1.91.0", override=True)
   ```

2. **Test compatibility:**
   ```bash
   conan remove "*" -c  # Clear cache
   conan install . --build=missing
   ```

3. **Document any breaking changes**

### Medium Term (Moderate Risk)

1. **Create custom recipe overlays** for critical packages
2. **Test with Conan 2.0** (currently using 2.25.1, so already on 2.X!)
3. **Submit ConanCenter PRs** for outdated recipes

### Long Term (Future Proofing)

1. **Migrate all dependencies** to Conan 2.X native packages
2. **Remove compatibility shims**
3. **Update CI/CD** to enforce Conan 2.X

## Current Status

**Good News:** We're already using Conan 2.25.1!
```
Conan version 2.25.1
```

**The warnings are coming from upstream packages** that haven't been updated yet. This is normal during the Conan 1.X → 2.X transition period.

**Impact on Blackhole:**
- ✅ Build system works fine (Conan 2.X is backward compatible)
- ⚠️ Warnings are cosmetic but indicate technical debt
- ⏳ Upstream packages will eventually update
- 🔧 We can accelerate by using newer versions or custom recipes

## Research: Package Update Status

### Checking ConanCenter for Updates

**Command to check available versions:**
```bash
conan search <package> -r conancenter
```

**Research Checklist:**

- [ ] boost: Current 1.90.0 → Check for 1.91.0+
- [ ] hdf5: Current 1.14.6 → Check for 1.14.7+ or 1.16.x
- [ ] bzip2: Current 1.0.8 → Check for 1.0.9+
- [ ] glbinding: Current 3.5.0 → Check for 3.6.0+
- [ ] taskflow: Current 3.10.0 → Check for 3.11.0+
- [ ] cli11: Current 2.6.0 → Check for 2.7.0+
- [ ] entt: Current 3.15.0 → Check for 3.16.0+
- [ ] xsimd: Current 13.2.0 → Check for 14.x

### Online Resources

**Official Conan 2.0 Migration Guide:**
- https://docs.conan.io/2.0/migrating_to_2.0.html
- https://docs.conan.io/2.0/reference/conanfile/methods/package_info.html

**ConanCenter Index:**
- https://github.com/conan-io/conan-center-index
- Search for package recipes and check commit history

**Conan 2.X Properties:**
- `cmake_target_name`: CMake target name (replaces `names`)
- `cmake_file_name`: Find file name (replaces `filenames`)
- `cmake_build_modules`: Build modules (replaces `build_modules`)
- `pkg_config_name`: pkg-config name

## Recommended Actions

### Now (While Build Completes)

1. **Search for updated package versions:**
   ```bash
   for pkg in boost hdf5 bzip2 glbinding taskflow cli11 entt xsimd; do
       echo "=== $pkg ==="
       conan search $pkg -r conancenter | tail -20
   done
   ```

2. **Check package update dates:**
   Visit ConanCenter and check when packages were last updated

3. **Test with newer versions:**
   Create `conanfile_test.py` with updated versions

### Later (After Build Verification)

1. **Incremental updates:**
   - Update one package at a time
   - Build and test after each update
   - Document any breaking changes

2. **Create custom recipes only if:**
   - Package is critical
   - No updated version available
   - Warnings block future Conan versions

3. **Contribute back:**
   - If we create working Conan 2.X recipes
   - Submit PR to ConanCenter
   - Help community

## Conclusion

**Current State:**
- Using Conan 2.25.1 ✅
- Deprecation warnings present ⚠️
- Build system functional ✅
- No immediate action required ✅

**Recommended Path:**
1. Monitor upstream package updates
2. Test newer package versions when available
3. Create custom recipes only if blocked
4. Warnings are informational, not critical

**Priority:** **LOW**
- Conan 2.X is backward compatible
- Warnings won't cause failures
- Can address gradually
- Focus on optimization and features first

## Next Steps

Once newer package versions are identified:

1. Update `conanfile.py` with version overrides
2. Test build with updated versions
3. Document any API changes
4. Update CONAN2_MIGRATION.md with results

**Tracking Issue:** Create GitHub issue for monitoring package updates

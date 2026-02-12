from conan import ConanFile
from conan.tools.cmake import cmake_layout


class BlackholeConan(ConanFile):
    name = "blackhole"
    version = "0.2"  # Bumped for Conan 2.x migration
    settings = "os", "arch", "compiler", "build_type"
    generators = ("CMakeDeps", "CMakeToolchain")

    # Conan 2.x native: Use set_property() for package configuration
    options = {
        "enable_ktx": [True, False],
        "enable_openimageio": [True, False],
        "enable_meshoptimizer": [True, False],
        "enable_shader_watcher": [True, False],
        "enable_fastnoise2": [True, False],
        "enable_eigen": [True, False],
    }

    default_options = {
        "hdf5/*:shared": True,
        "spdlog/*:shared": True,
        "fmt/*:shared": True,
        "boost/*:without_cobalt": True,
        "enable_ktx": False,
        "enable_openimageio": False,
        "enable_meshoptimizer": True,
        "enable_shader_watcher": True,
        "enable_fastnoise2": True,
        "enable_eigen": True,
    }

    def requirements(self):
        """
        Updated to latest Conan 2.x compatible versions (2026-02-11)
        All packages verified in ConanCenter with Conan 2.x support
        """
        # Window & Input (OpenGL-native)
        self.requires("glfw/3.4")                    # Latest, Conan 2.x native

        # OpenGL Binding & Math
        self.requires("glbinding/3.5.0")             # Latest, Conan 2.x native
        self.requires("glm/1.0.1")                   # Latest, Conan 2.x native

        # SIMD & Performance
        self.requires("xsimd/14.0.0", override=True) # UPGRADED: 13.2.0 → 14.0.0
        self.requires("highway/1.3.0")               # UPGRADED: 1.2.0 → 1.3.0
        self.requires("sleef/3.9.0")                 # Latest

        # ECS & Utilities
        self.requires("entt/3.16.0")                 # UPGRADED: 3.15.0 → 3.16.0
        self.requires("pcg-cpp/cci.20220409")        # Latest
        self.requires("taskflow/3.10.0")             # Latest

        # UI & Rendering
        self.requires("imgui/1.92.5-docking", override=True)  # Latest docking branch
        self.requires("imguizmo/cci.20231114")       # Latest
        self.requires("rmlui/6.1")                   # Latest

        # Serialization
        self.requires("flatbuffers/25.9.23")         # Latest

        # Data & I/O
        self.requires("hdf5/1.14.6", override=True)  # Latest
        self.requires("highfive/3.1.1")              # Latest

        # Logging & Formatting
        self.requires("spdlog/1.17.0")               # UPGRADED: 1.16.0 → 1.17.0
        self.requires("fmt/12.1.0", override=True)   # Latest

        # Profiling & Debugging
        self.requires("tracy/0.13.1")                # Latest

        # CLI & Configuration
        self.requires("cli11/2.6.0")                 # Latest

        # Boost Libraries
        self.requires("boost/1.90.0")                # Latest stable

        # Math Libraries
        self.requires("gmp/6.3.0")                   # Latest
        self.requires("mpfr/4.2.2")                  # Latest

        # Image Processing
        self.requires("stb/cci.20240531")            # Latest

        # Theorem Proving
        self.requires("z3/4.15.4")                   # UPGRADED: 4.14.1 → 4.15.4

        # Testing
        self.requires("gtest/1.17.0")                # UPGRADED: 1.14.0 → 1.17.0

        # Optional Dependencies
        if self.options.enable_meshoptimizer:
            self.requires("meshoptimizer/1.0")       # UPGRADED: 0.25 → 1.0

        if self.options.enable_shader_watcher:
            self.requires("watcher/0.14.1")          # Latest

        if self.options.enable_fastnoise2:
            self.requires("fastnoise2/0.10.0-alpha") # Only version

        if self.options.enable_ktx:
            self.requires("ktx/4.3.2")               # Latest

        if self.options.enable_openimageio:
            self.requires("openimageio/3.1.8.0")     # Latest

        if self.options.enable_eigen:
            # Using 3.4.1 instead of 5.x due to potential API breaks
            self.requires("eigen/3.4.1")             # UPGRADED: 3.4.0 → 3.4.1

    def layout(self):
        """Conan 2.x native layout"""
        cmake_layout(self, build_folder=".")

    def configure(self):
        """Conan 2.x: Configure package options"""
        # Ensure compatibility with Conan 2.x
        pass

    def validate(self):
        """Conan 2.x: Validate configuration"""
        # C++17 minimum requirement
        if self.settings.compiler.get_safe("cppstd"):
            if int(str(self.settings.compiler.cppstd)) < 17:
                raise ConanInvalidConfiguration("Blackhole requires C++17 or later")

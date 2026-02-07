from conan import ConanFile
from conan.tools.cmake import cmake_layout


class BlackholeConan(ConanFile):
    name = "blackhole"
    version = "0.1"
    settings = "os", "arch", "compiler", "build_type"
    generators = ("CMakeDeps", "CMakeToolchain")
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
        self.requires("glfw/3.4")
        self.requires("glbinding/3.5.0")
        self.requires("glm/1.0.1")
        self.requires("xsimd/13.2.0", override=True)
        self.requires("highway/1.2.0")
        self.requires("sleef/3.9.0")
        self.requires("entt/3.15.0")
        self.requires("pcg-cpp/cci.20220409")
        self.requires("taskflow/3.10.0")
        self.requires("imgui/1.92.5-docking", override=True)
        self.requires("imguizmo/cci.20231114")
        self.requires("rmlui/6.1")
        self.requires("flatbuffers/25.9.23")
        self.requires("hdf5/1.14.6", override=True)
        self.requires("highfive/3.1.1")
        self.requires("spdlog/1.16.0")
        self.requires("fmt/12.1.0", override=True)
        self.requires("tracy/0.13.1")
        self.requires("cli11/2.6.0")
        self.requires("boost/1.90.0")
        self.requires("gmp/6.3.0")
        self.requires("mpfr/4.2.2")
        self.requires("stb/cci.20240531")
        self.requires("z3/4.14.1")
        self.requires("gtest/1.14.0")
        if self.options.enable_meshoptimizer:
            self.requires("meshoptimizer/0.25")
        if self.options.enable_shader_watcher:
            self.requires("watcher/0.14.1")
        if self.options.enable_fastnoise2:
            self.requires("fastnoise2/0.10.0-alpha")
        if self.options.enable_ktx:
            self.requires("ktx/4.3.2")
        if self.options.enable_openimageio:
            self.requires("openimageio/3.1.8.0")
        if self.options.enable_eigen:
            self.requires("eigen/3.4.0")

    def layout(self):
        cmake_layout(self, build_folder=".")

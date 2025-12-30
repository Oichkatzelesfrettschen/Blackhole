from conan import ConanFile
from conan.tools.cmake import cmake_layout


class BlackholeConan(ConanFile):
    name = "blackhole"
    version = "0.1"
    settings = "os", "arch", "compiler", "build_type"
    generators = ("CMakeDeps", "CMakeToolchain")
    default_options = {
        "hdf5/*:shared": True,
        "spdlog/*:shared": True,
        "fmt/*:shared": True,
        "boost/*:without_cobalt": True,
    }

    def requirements(self):
        self.requires("glfw/3.4")
        self.requires("glbinding/3.5.0")
        self.requires("glm/cci.20230113")
        self.requires("xsimd/13.2.0", override=True)
        self.requires("entt/3.15.0")
        self.requires("pcg-cpp/cci.20220409")
        self.requires("taskflow/3.10.0")
        self.requires("imgui/1.92.5-docking", override=True)
        self.requires("imguizmo/cci.20231114")
        self.requires("rmlui/4.4")
        self.requires("flatbuffers/25.9.23")
        self.requires("hdf5/1.14.6", override=True)
        self.requires("highfive/3.1.1")
        self.requires("spdlog/1.16.0")
        self.requires("fmt/12.1.0", override=True)
        self.requires("tracy/0.12.2")
        self.requires("cli11/2.6.0")
        self.requires("boost/1.90.0")
        self.requires("stb/cci.20240531")
        self.requires("z3/4.14.1")

    def layout(self):
        cmake_layout(self)

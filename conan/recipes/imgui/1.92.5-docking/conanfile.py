from conan import ConanFile
from conan.tools.cmake import CMake, CMakeDeps, CMakeToolchain, cmake_layout
from conan.tools.files import copy, get
import os


class ImGuiConan(ConanFile):
    name = "imgui"
    version = "1.92.5-docking"
    license = "MIT"
    url = "https://github.com/ocornut/imgui"
    description = "Immediate mode GUI"
    package_type = "library"

    settings = "os", "arch", "compiler", "build_type"
    options = {"shared": [True, False], "fPIC": [True, False], "demo": [True, False]}
    default_options = {"shared": False, "fPIC": True, "demo": True}

    exports_sources = "CMakeLists.txt"

    def layout(self):
        cmake_layout(self)

    def generate(self):
        toolchain = CMakeToolchain(self)
        toolchain.variables["IMGUI_BUILD_DEMO"] = self.options.demo
        toolchain.generate()
        deps = CMakeDeps(self)
        deps.generate()

    def source(self):
        get(self, **self.conan_data["sources"][self.version], strip_root=True)

    def build(self):
        cmake = CMake(self)
        cmake.configure()
        cmake.build()

    def package(self):
        cmake = CMake(self)
        cmake.install()
        copy(self, "LICENSE.txt", src=self.source_folder, dst=os.path.join(self.package_folder, "licenses"))

    def package_info(self):
        self.cpp_info.libs = ["imgui"]
        self.cpp_info.set_property("cmake_file_name", "imgui")
        self.cpp_info.set_property("cmake_target_name", "imgui::imgui")

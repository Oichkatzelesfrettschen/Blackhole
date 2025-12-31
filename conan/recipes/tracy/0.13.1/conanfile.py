from conan import ConanFile
from conan.tools.cmake import CMake, CMakeDeps, CMakeToolchain, cmake_layout
from conan.tools.files import copy, get
import os


class TracyConan(ConanFile):
    name = "tracy"
    version = "0.13.1"
    license = "BSD-3-Clause"
    url = "https://github.com/wolfpld/tracy"
    description = "Real-time profiler"
    package_type = "library"

    settings = "os", "arch", "compiler", "build_type"
    options = {"shared": [True, False], "fPIC": [True, False], "on_demand": [True, False]}
    default_options = {"shared": False, "fPIC": True, "on_demand": False}

    def layout(self):
        cmake_layout(self)

    def generate(self):
        toolchain = CMakeToolchain(self)
        toolchain.variables["TRACY_ENABLE"] = "ON"
        toolchain.variables["TRACY_ON_DEMAND"] = "ON" if self.options.on_demand else "OFF"
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
        copy(self, "LICENSE", src=self.source_folder, dst=os.path.join(self.package_folder, "licenses"))

    def package_info(self):
        self.cpp_info.libs = ["TracyClient"]
        self.cpp_info.includedirs.append(os.path.join("include", "tracy"))
        self.cpp_info.libdirs.append(os.path.join("lib", str(self.settings.build_type)))
        self.cpp_info.set_property("cmake_file_name", "Tracy")
        self.cpp_info.set_property("cmake_target_name", "Tracy::TracyClient")

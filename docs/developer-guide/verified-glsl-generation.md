# Verified C++ names and maintained GLSL interfaces

The verified C++ headers use lowerCamelCase functions and members, with uppercase
global constants. Existing shader callers use a separate GLSL interface with
names such as `schwarzschild_g_tt`, `sv_add`, and `MetricComponents.g_tt`.
`scripts/cpp_to_glsl.py` preserves that interface through `GLSL_PUBLIC_NAMES`.
The adapter maps complete code identifiers before parsing and preserves comments,
character literals, and ordinary or raw string literals. Explicit spellings
retain acronym boundaries such as
`E_z` and `compute_E_z`.

`shader/raytracer.frag` includes the maintained Schwarzschild, Kerr, RK4,
geodesic, energy-constraint, and null-constraint GLSL files. The embedded shaders
in `tests/gpu_cpu_parity_test.cpp` also use the maintained Schwarzschild, EOS,
cosmology, RK4, and geodesic interfaces. These callers retain their GLSL names.
`shader/include/verified/physics.glsl` is a separate manual implementation used
by `blackhole_main.frag` and `geodesic_trace.comp`; the generator leaves that file
outside its ten-header input list.

## Generation boundary

The CMake `generate_glsl` target invokes the generator and writes into the source
shader directory. The script reports translation and file-writing outcomes;
the script does not compile its output. A missing input or a per-file translation
exception increments the failure counter and makes the CLI exit with status 1.
The script retains individual errors and completes the other requested inputs.
Maintained GLSL files contain manual
lowerings that the regex generator cannot reproduce. Baseline scratch generation
differs from six maintained files before any C++ identifier changes:

| Output | Unsupported or divergent lowering |
| --- | --- |
| `rk4.glsl` | Struct-field parsing consumes comment text and member bodies; emitted uniform blocks replace value structs; aggregate braces, `static_cast`, and scoped enum values remain C++ syntax. |
| `geodesic.glsl` | Struct comments become fields; callable Christoffel members require a GLSL representation; lambda factories, aggregate construction, and orbit enums remain C++ syntax. |
| `cosmology.glsl` | Struct parsing, casts, `std::size_t`, `std::log10`, and `std::numbers::pi` require lowering; same-name overload ordering drops the `FlatLCDM` overload used by other functions. |
| `eos.glsl` | Struct comments become field declarations and a uniform block replaces the maintained value struct. |
| `energy_conserving_geodesic.glsl` | An unnamed mass parameter is omitted from a signature; `std::max`, aggregates, template callables, and inferred local types require lowering. |
| `null_constraint.glsl` | Callback-based RK4 steps, metric functions, aggregates, casts, and nested braces exceed the parser's lowering rules. |

The maintained energy and null-constraint files also contain incomplete callback
adaptations. Their compilation establishes syntax acceptance, rather than
equivalence to the C++ callback integrators. Existing generated banner claims
about mathematical proof, GPU precision, occupancy, and frame rate require
independent evidence; file generation does not establish those claims.

The naming adapter preserves the generator's existing translation behavior.
It leaves these lowering defects visible and preserves the maintained shader
files. A future lowering repair must validate both generated syntax and the
numeric or callback semantics before replacing the maintained files.

## Repeatable checks

Generate into an isolated directory when investigating the translator. Set
`PYTHON` to the intended interpreter, then run from the repository root:

```sh
"$PYTHON" - <<'PY'
import sys
from pathlib import Path

sys.path.insert(0, "scripts")
from cpp_to_glsl import CPPToGLSLTranspiler

transpiler = CPPToGLSLTranspiler(
    Path("src/physics/verified"), Path("build/verified-glsl-generation")
)
transpiler.transpile_all()
raise SystemExit(bool(transpiler.transpilation_stats["files_failed"]))
PY
```

The naming check compares scratch output from retained baseline headers with
scratch output from the same headers after the recorded public identifier renames.
Remove comments and whitespace before comparing code tokens. Check every public
alias independently,
including identifier boundaries and preservation of comments and strings.
This comparison establishes naming compatibility even when both outputs retain
the same unsupported C++ constructs.

`"$PYTHON" tests/cpp_to_glsl_test.py` exercises a synthetic header through file
transpilation and checks function, member, and constant names. The regression
also covers every alias boundary, unchanged identifiers, comments, escaped
strings, raw strings, and character literals. Subprocess regressions verify CLI
success, missing-input failure, and translation-exception failure while retaining
the other nine generated outputs.

Run `ctest --test-dir build/CI -R '^shader_validation$' --output-on-failure`
to validate the maintained shader entrypoints with the configured shader
warning policy. That command validates the maintained source shader tree;
it does not validate the isolated regenerated files or execute GPU kernels.

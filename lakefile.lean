import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

package Vericoding where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]
  releaseRepo := "https://github.com/Beneficial-AI-Foundation/vericoding"
  buildArchive := "Vericoding-{OS}-{ARCH}.tar.gz"
  preferReleaseBuild := true

/-!
# Vericoding Project Structure

This project contains formal specifications and verifications ported from various sources,
particularly Dafny benchmarks and NumPy specifications.
-/

@[default_target]
lean_lib Vericoding where
  globs := #[.andSubmodules `Vericoding]
  srcDir := "lean"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, false⟩
  ]

@[default_target]
lean_lib Benchmarks where
  globs := #[.andSubmodules `Benchmarks]
  srcDir := "lean"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, false⟩
  ]
@[default_target]
lean_lib NumpyHoareTriple where
  globs := #[.andSubmodules `NumpyHoareTriple]
  srcDir := "lean"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    -- docs are important here
    ⟨`linter.missingDocs, true⟩
  ]

lean_lib BenchmarksGenerated where
  globs := #[.andSubmodules `BenchmarksGenerated]
  srcDir := "lean"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

lean_lib DafnyBenchSpecs where
  globs := #[.andSubmodules `DafnyBenchSpecs]
  srcDir := "lean"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

@[default_target]
lean_exe vericoding where
  root := `Main
  srcDir := "lean"
  supportInterpreter := true
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

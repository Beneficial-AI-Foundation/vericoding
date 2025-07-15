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
  -- Main library configuration - root file only
  globs := #[.one `Vericoding]
  srcDir := "lean-vc"

/-- Benchmarks library for specs -/
lean_lib Benchmarks where
  globs := #[.andSubmodules `benchmarks]
  srcDir := "lean-vc"

/-- NumPy specifications using Hoare triple syntax -/
lean_lib NumpyHoareTriple where
  globs := #[.andSubmodules `numpy_hoare_triple]
  srcDir := "lean-vc"

@[default_target]
lean_exe vericoding where
  root := `Main
  supportInterpreter := true

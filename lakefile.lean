import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

package Vericoding where
  version := v!"0.1.0"
  -- Disable missingDocs noise for now; too many undocumented funcs
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, false⟩
  ]
  releaseRepo := "https://github.com/Beneficial-AI-Foundation/vericoding"
  buildArchive := "Vericoding-{OS}-{ARCH}.tar.gz"
  preferReleaseBuild := true

/-!
# Vericoding Project Structure

This project contains formal specifications and verifications ported from various sources,
particularly Dafny benchmarks and NumPy specifications.
-/


lean_lib BenchmarksGenerated where
  globs := #[.andSubmodules `BenchmarksGenerated]
  srcDir := "lean"

lean_lib DafnyBenchSpecs where
  globs := #[.andSubmodules `DafnyBenchSpecs]

lean_lib HumanEval where
  globs := #[.andSubmodules `humaneval]
  srcDir := "benchmarks/lean"

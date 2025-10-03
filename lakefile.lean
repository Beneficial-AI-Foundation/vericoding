import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0-rc2"

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

-- vericoder.py puts files here
lean_lib Generated where
  globs := #[.andSubmodules `Generated]
  srcDir := "lean"

-- Original benchmark files + all vericoder generated files
lean_lib Benchmarks where
  globs := #[
    .submodules `fvapps.files,
    .submodules `dafnybench.files,
    .submodules `clever.files,
    .submodules `numpy_simple.files,
    .submodules `numpy_triple.files,
    .submodules `verina.files,
    .submodules `test.files,
    -- Include all subdirectories (including test and vericoder_* output dirs)
    .andSubmodules `apps,
    .andSubmodules `bignum,
    .andSubmodules `clever,
    .andSubmodules `dafnybench,
    .andSubmodules `fvapps,
    .andSubmodules `numpy_simple,
    .andSubmodules `numpy_triple,
    .andSubmodules `test,
    .andSubmodules `verified_cogen,
    .andSubmodules `verina,
  ]
  srcDir := "benchmarks/lean"


lean_lib BenchmarksCheckedInCI where
  globs := #[
    .submodules `fvapps.files,
    .submodules `dafnybench.files,
    .submodules `clever.files,
    .submodules `numpy_simple.files,
    .submodules `numpy_triple.files,
    .submodules `verina.files,
  ]
  srcDir := "benchmarks/lean"

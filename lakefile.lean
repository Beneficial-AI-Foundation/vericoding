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

-- not required any longer?
-- lean_lib BenchmarksGenerated where
--   globs := #[.andSubmodules `BenchmarksGenerated]
--   srcDir := "lean"

-- not required any longer?
-- lean_lib DafnyBenchSpecs where
--   globs := #[.andSubmodules `DafnyBenchSpecs]

-- vericoder.py puts files here
lean_lib Generated where
  globs := #[.andSubmodules `Generated]
  srcDir := "lean"

-- Original benchmark files + all vericoder generated files
lean_lib Benchmarks where
  globs := #[
    .submodules `apps.files,
    .submodules `dafnybench.poor.unformatted,
    .submodules `clever.files,
    .submodules `numpy_simple.poor.unformatted,
    .submodules `numpy_triple.files,
    .submodules `verina.files,
    -- Include all subdirectories (including vericoder_* dirs)
    .andSubmodules `apps,
    .andSubmodules `bignum,
    .andSubmodules `dafnybench,
    .andSubmodules `humaneval,
    .andSubmodules `humaneval_clever,
    .andSubmodules `numpy_simple,
    .andSubmodules `numpy_triple,
    .andSubmodules `verina,
  ]
  srcDir := "benchmarks/lean"


lean_lib BenchmarksCheckedInCI where
  globs := #[
    .submodules `apps.files,
    .submodules `dafnybench.poor.unformatted,
    .submodules `humaneval.files,
    .submodules `numpy_simple.poor.unformatted,
    .submodules `numpy_triple.files,
    .submodules `verina.files,
  ]
  srcDir := "benchmarks/lean"

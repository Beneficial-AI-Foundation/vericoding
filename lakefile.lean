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

/-!
Split the monolithic `Benchmarks` library into sub-targets so we can
build subsets quickly and compose them via `needs`.

Sub‑targets map one‑to‑one to major subdirectories of `benchmarks/lean`.
The aggregate targets `Benchmarks.Fast` and `Benchmarks.All` use `needs`
to compose these pieces.
-/

-- Apps (files)
lean_lib BenchApps where
  globs := #[.submodules `apps.files]
  srcDir := "benchmarks/lean"

-- Bignum variants
lean_lib BenchBignumJK where
  globs := #[.submodules `bignum_jk]
  srcDir := "benchmarks/lean"

lean_lib BenchBignumOB where
  globs := #[.submodules `bignum_ob]
  srcDir := "benchmarks/lean"

-- Dafny benchmarks
lean_lib BenchDafny where
  globs := #[.submodules `dafnybench]
  srcDir := "benchmarks/lean"

lean_lib BenchDafnyAB where
  globs := #[.submodules `dafnybench_ab]
  srcDir := "benchmarks/lean"

-- Humaneval
@[default_target]
lean_lib BenchHumaneval where
  globs := #[.submodules `humaneval.files]
  srcDir := "benchmarks/lean"

-- Verina
lean_lib BenchVerina where
  globs := #[.submodules `verina.files]
  srcDir := "benchmarks/lean"

-- Numpy
lean_lib BenchNumpySimple where
  globs := #[.submodules `numpy_simple]
  srcDir := "benchmarks/lean"

lean_lib BenchNumpyTriple where
  globs := #[.submodules `numpy_triple.files]
  srcDir := "benchmarks/lean"

/-!
Aggregate targets using `needs`.

`Benchmarks.Fast` collects smaller suites that are quick to iterate on
and is marked as a default target.

`Benchmarks.All` depends on all sub‑targets and can be built via
`lake build Benchmarks.All`.
-/

@[default_target]
lean_lib Benchmarks.Fast where
  srcDir := "benchmarks/lean" -- unused; present to satisfy `lean_lib`
  globs := #[] -- no modules of its own; acts as an aggregator
  needs := #[
    -- smaller/faster suites (keep build green)
    .packageTarget .anonymous `BenchHumaneval
  ]

lean_lib Benchmarks.All where
  srcDir := "benchmarks/lean" -- unused; present to satisfy `lean_lib`
  globs := #[] -- no modules of its own; acts as an aggregator
  needs := #[
    .packageTarget .anonymous `BenchApps,
    .packageTarget .anonymous `BenchBignumJK,
    .packageTarget .anonymous `BenchBignumOB,
    .packageTarget .anonymous `BenchDafny,
    .packageTarget .anonymous `BenchDafnyAB,
    .packageTarget .anonymous `BenchHumaneval,
    .packageTarget .anonymous `BenchVerina,
    .packageTarget .anonymous `BenchNumpySimple,
    .packageTarget .anonymous `BenchNumpyTriple
  ]

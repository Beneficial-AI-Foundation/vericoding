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
  -- Main library configuration
  -- `.andSubmodules` ensures that all `.lean` files in the `Vericoding` directory are built.
  -- TODO: split out the `code_from_spec` library into a separate `lean_lib` that `needs` this `lean_lib` which provides the specs.
  globs := #[.andSubmodules `Benchmarks]
  srcDir := "lean-vc"

@[default_target]
lean_exe vericoding where
  root := `Main
  supportInterpreter := true

import Lake
open Lake DSL

/-- Main NumpySpec package -/
package NumpySpec where
  -- Lean options (typechecked!)
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]
  -- Cloud release configuration for pre-built artifacts
  releaseRepo := "https://github.com/Beneficial-AI-Foundation/NumpySpec"
  buildArchive := "NumpySpec-{OS}-{ARCH}.tar.gz"
  preferReleaseBuild := true
  -- Weak configuration arguments that don't trigger rebuilds
  weakLeanArgs := #[
    "-Dpp.unicode.fun=true"  -- Pretty printing options
  ]

/-! Dependencies (order matters for compilation) -/

/-- Used for documentation generation -/
require verso from git "https://github.com/leanprover/verso" @ "main"

/-- Used for Tactic Programming Guide examples -/
require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
require Qq from git "https://github.com/leanprover-community/quote4" @ "master"

-- Used for theorem proving. *Must* come before `mathlib` to avoid recompiling `mathlib`.
-- COMMENTED OUT FOR SPEED: LeanHammer forces mathlib rebuild, taking >10 minutes
-- require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "temp-v4.21.0-rc3"

-- Used for math library
-- COMMENTED OUT FOR SPEED: mathlib takes too long to build initially
-- require mathlib from git "https://github.com/leanprover-community/mathlib4"

/-- Main library -/
lean_lib NumpySpec where
  -- Include the root module and all submodules
  globs := #[.andSubmodules `NumpySpec]

/-- FuncTracker sublibrary for 2D function tracking tables -/
lean_lib FuncTracker where
  -- Include all FuncTracker modules
  globs := #[.andSubmodules `FuncTracker]

/-- DafnySpecs library for ported Dafny specifications -/
lean_lib DafnySpecs where
  -- Include all DafnySpecs modules
  globs := #[.andSubmodules `DafnySpecs]

/-- Main library. NumPy-compatible n-dimensional arrays -/
@[default_target]
lean_lib NDArray where
  -- Include all NDArray modules
  globs := #[.andSubmodules `NDArray]

/-- Executables -/
@[default_target]
lean_exe numpyspec where
  root := `Main

-- lean_exe numpyspecmanual where
--   root := `NumpySpec.ManualMain

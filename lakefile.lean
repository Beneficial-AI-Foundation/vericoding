import Lake
open Lake DSL

package "vericoding" where
  version := v!"0.1.0"

/-!
# Vericoding Project Structure

This project contains formal specifications and verifications ported from various sources,
particularly Dafny benchmarks and NumPy specifications.

## Main Libraries:
- `Vericoding`: Core library with basic definitions
- `Vericoding.Benchmarks.DafnySpecs`: Dafny benchmark specifications (from lean4/ directory)

Note: The lean4/benchmarks/dafny-bench_specs directory contains standalone Lean 4 ports
of Dafny specifications. These are not currently integrated into the main build but
can be referenced as examples.
-/

lean_lib «Vericoding» where
  -- Main library configuration
  globs := #[.andSubmodules `Vericoding]

-- TODO: Add library for lean4/benchmarks/dafny-bench_specs when ready to integrate
-- lean_lib «VericodingBenchmarks» where
--   srcDir := "lean4/benchmarks/dafny-bench_specs"
--   roots := #[`Abs, `AddOne, `AllDigits] -- etc.

@[default_target]
lean_exe "vericoding" where
  root := `Main
  supportInterpreter := true

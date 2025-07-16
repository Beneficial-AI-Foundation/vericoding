import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Synthesis Task: Nth Hexagonal Number

This module ports the Dafny synthesis task for calculating the nth hexagonal number.

The specification includes:
- A method `nthHexagonalNumber` that returns the nth hexagonal number
- Requires n to be non-negative
- Ensures the result equals n × (2n - 1)
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisNthHexagonalNumber

/-- Implementation placeholder for nthHexagonalNumber -/
def nthHexagonalNumber (n : Int) : Id Int := sorry

/-- Hoare triple for nthHexagonalNumber -/
theorem nthHexagonalNumber_spec (n : Int) 
    (h : n ≥ 0) :
    ⦃⌜n ≥ 0⌝⦄ 
    nthHexagonalNumber n
    ⦃⇓hexNum => ⌜hexNum = n * ((2 * n) - 1)⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisNthHexagonalNumber
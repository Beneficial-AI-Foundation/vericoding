import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Synthesis Task: Is Non-Prime

This module ports the Dafny synthesis task for checking if a number is non-prime (composite).

The specification includes:
- A method `isNonPrime` that returns true if the number is composite
- Requires n ≥ 2
- Ensures the result is true if and only if there exists a divisor k where 2 ≤ k < n
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisIsNonPrime

/-- Implementation placeholder for isNonPrime -/
def isNonPrime (n : Int) : Id Bool := sorry

/-- Hoare triple for isNonPrime -/
theorem isNonPrime_spec (n : Int) 
    (h : n ≥ 2) :
    ⦃⌜n ≥ 2⌝⦄ 
    isNonPrime n
    ⦃⇓result => ⌜result ↔ ∃ k : Int, 2 ≤ k ∧ k < n ∧ n % k = 0⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisIsNonPrime
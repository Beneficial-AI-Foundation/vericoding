import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- NthNonagonalNumber satisfies the following properties. -/
def NthNonagonalNumber (n : Int) : Id Unit :=
  sorry

/-- Specification: NthNonagonalNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem NthNonagonalNumber_spec (n : Int) :
    ⦃⌜True⌝⦄
    NthNonagonalNumber n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- NthOctagonalNumber satisfies the following properties. -/
def NthOctagonalNumber (n : Int) : Id Unit :=
  sorry

/-- Specification: NthOctagonalNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem NthOctagonalNumber_spec (n : Int) :
    ⦃⌜True⌝⦄
    NthOctagonalNumber n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

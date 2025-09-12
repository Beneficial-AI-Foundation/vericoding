import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- NthDecagonalNumber satisfies the following properties. -/
def NthDecagonalNumber (n : Int) : Id Unit :=
  sorry

/-- Specification: NthDecagonalNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem NthDecagonalNumber_spec (n : Int) :
    ⦃⌜True⌝⦄
    NthDecagonalNumber n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

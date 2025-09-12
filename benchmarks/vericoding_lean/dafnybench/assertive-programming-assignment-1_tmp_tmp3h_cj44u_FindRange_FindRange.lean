import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindRange satisfies the following properties. -/
def FindRange (q : List Int) : Id Unit :=
  sorry

/-- Specification: FindRange satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindRange_spec (q : List Int) :
    ⦃⌜True⌝⦄
    FindRange q
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

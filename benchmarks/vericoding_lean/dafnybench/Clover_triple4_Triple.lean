import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Triple satisfies the following properties. -/
def Triple (x : Int) : Id Unit :=
  sorry

/-- Specification: Triple satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Triple_spec (x : Int) :
    ⦃⌜True⌝⦄
    Triple x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

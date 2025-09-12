import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- parent satisfies the following properties. -/
def parent (idx : Int) : Id Unit :=
  sorry

/-- Specification: parent satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem parent_spec (idx : Int) :
    ⦃⌜True⌝⦄
    parent idx
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

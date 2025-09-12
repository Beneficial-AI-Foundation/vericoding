import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- NinetyOne satisfies the following properties. -/
def NinetyOne (x : Int) : Id Unit :=
  sorry

/-- Specification: NinetyOne satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem NinetyOne_spec (x : Int) :
    ⦃⌜True⌝⦄
    NinetyOne x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

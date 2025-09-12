import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- PlusOne satisfies the following properties. -/
def PlusOne (x : Int) : Id Unit :=
  sorry

/-- Specification: PlusOne satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem PlusOne_spec (x : Int) :
    ⦃⌜True⌝⦄
    PlusOne x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

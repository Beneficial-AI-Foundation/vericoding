import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Sum satisfies the following properties. -/
def Sum (x : Int) : Id Unit :=
  sorry

/-- Specification: Sum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Sum_spec (x : Int) :
    ⦃⌜True⌝⦄
    Sum x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

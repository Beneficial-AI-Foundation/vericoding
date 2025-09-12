import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- remove_front satisfies the following properties. -/
def remove_front (a : Array Int) : Id Unit :=
  sorry

/-- Specification: remove_front satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem remove_front_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    remove_front a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

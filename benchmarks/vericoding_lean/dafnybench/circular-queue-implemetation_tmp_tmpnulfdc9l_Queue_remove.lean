import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- remove satisfies the following properties. -/
def remove (item : Int) : Id Unit :=
  sorry

/-- Specification: remove satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem remove_spec (item : Int) :
    ⦃⌜True⌝⦄
    remove item
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

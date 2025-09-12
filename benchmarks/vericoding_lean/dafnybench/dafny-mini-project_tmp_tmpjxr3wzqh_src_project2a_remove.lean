import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- remove satisfies the following properties. -/
def remove (m : Message) : Id Unit :=
  sorry

/-- Specification: remove satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem remove_spec (m : Message) :
    ⦃⌜True⌝⦄
    remove m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

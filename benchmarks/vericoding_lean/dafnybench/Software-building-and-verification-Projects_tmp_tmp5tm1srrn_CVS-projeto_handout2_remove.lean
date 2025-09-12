import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- remove satisfies the following properties. -/
def remove (k : K) : Id Unit :=
  sorry

/-- Specification: remove satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem remove_spec (k : K) :
    ⦃⌜True⌝⦄
    remove k
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

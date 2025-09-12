import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- M satisfies the following properties. -/
def M (s : set<int>) : Id Unit :=
  sorry

/-- Specification: M satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem M_spec (s : set<int>) :
    ⦃⌜True⌝⦄
    M s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Merge satisfies the following properties. -/
def Merge (b : Array Int) : Id Unit :=
  sorry

/-- Specification: Merge satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Merge_spec (b : Array Int) :
    ⦃⌜True⌝⦄
    Merge b
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

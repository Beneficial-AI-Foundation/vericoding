import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Search1000 satisfies the following properties. -/
def Search1000 (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Search1000 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Search1000_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Search1000 a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- count satisfies the following properties. -/
def count (v : Int) : Id Unit :=
  sorry

/-- Specification: count satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem count_spec (v : Int) :
    ⦃⌜True⌝⦄
    count v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

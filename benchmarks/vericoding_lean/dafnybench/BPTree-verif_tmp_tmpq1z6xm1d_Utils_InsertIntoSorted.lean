import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- count satisfies the following properties. -/
def count (a : seq<bool>) : Id Unit :=
  sorry

/-- Specification: count satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem count_spec (a : seq<bool>) :
    ⦃⌜True⌝⦄
    count a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

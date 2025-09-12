import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- vector_Sum satisfies the following properties. -/
def vector_Sum (v : List Int) : Id Unit :=
  sorry

/-- Specification: vector_Sum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem vector_Sum_spec (v : List Int) :
    ⦃⌜True⌝⦄
    vector_Sum v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

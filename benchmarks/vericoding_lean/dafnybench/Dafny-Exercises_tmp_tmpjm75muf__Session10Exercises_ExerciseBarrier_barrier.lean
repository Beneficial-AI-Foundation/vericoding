import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- barrier satisfies the following properties. -/
def barrier (v : Array Int) : Id Unit :=
  sorry

/-- Specification: barrier satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem barrier_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    barrier v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- max satisfies the following properties. -/
def max (x : Int) : Id Unit :=
  sorry

/-- Specification: max satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem max_spec (x : Int) :
    ⦃⌜True⌝⦄
    max x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

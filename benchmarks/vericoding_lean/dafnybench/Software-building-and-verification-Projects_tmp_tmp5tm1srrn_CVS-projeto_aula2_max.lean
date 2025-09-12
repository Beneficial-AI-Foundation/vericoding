import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- max satisfies the following properties. -/
def max (a : Int) : Id Unit :=
  sorry

/-- Specification: max satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem max_spec (a : Int) :
    ⦃⌜True⌝⦄
    max a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

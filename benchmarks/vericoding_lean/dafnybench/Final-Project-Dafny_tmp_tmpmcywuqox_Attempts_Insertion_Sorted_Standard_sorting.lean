import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sorting satisfies the following properties. -/
def sorting (Array : Array Int) : Id Unit :=
  sorry

/-- Specification: sorting satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sorting_spec (Array : Array Int) :
    ⦃⌜True⌝⦄
    sorting Array
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

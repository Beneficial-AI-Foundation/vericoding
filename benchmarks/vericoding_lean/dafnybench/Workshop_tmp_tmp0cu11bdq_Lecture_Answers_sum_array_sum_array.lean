import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sum_array satisfies the following properties. -/
def sum_array (a : Array Int) : Id Unit :=
  sorry

/-- Specification: sum_array satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sum_array_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    sum_array a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

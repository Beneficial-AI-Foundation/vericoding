import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sum satisfies the following properties. -/
def sum (s : Array Int) : Id Unit :=
  sorry

/-- Specification: sum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sum_spec (s : Array Int) :
    ⦃⌜True⌝⦄
    sum s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

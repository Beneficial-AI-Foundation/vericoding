import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- swap3 satisfies the following properties. -/
def swap3 (a : Array Int) : Id Unit :=
  sorry

/-- Specification: swap3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem swap3_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    swap3 a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

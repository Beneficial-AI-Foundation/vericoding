import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mmaximum1 satisfies the following properties. -/
def mmaximum1 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mmaximum1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mmaximum1_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mmaximum1 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mmaximum2 satisfies the following properties. -/
def mmaximum2 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mmaximum2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mmaximum2_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mmaximum2 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- m1 satisfies the following properties. -/
def m1 (x : Int) : Id Unit :=
  sorry

/-- Specification: m1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem m1_spec (x : Int) :
    ⦃⌜True⌝⦄
    m1 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- A1 satisfies the following properties. -/
def A1 (x : Int) : Id Unit :=
  sorry

/-- Specification: A1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem A1_spec (x : Int) :
    ⦃⌜True⌝⦄
    A1 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Minimum satisfies the following properties. -/
def Minimum (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Minimum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Minimum_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Minimum a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

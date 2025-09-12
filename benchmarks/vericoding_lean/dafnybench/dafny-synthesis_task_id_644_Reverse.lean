import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Reverse satisfies the following properties. -/
def Reverse (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Reverse satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Reverse_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Reverse a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

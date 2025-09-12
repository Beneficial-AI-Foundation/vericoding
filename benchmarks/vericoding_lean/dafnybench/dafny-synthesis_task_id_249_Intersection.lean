import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Intersection satisfies the following properties. -/
def Intersection (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Intersection satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Intersection_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Intersection a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

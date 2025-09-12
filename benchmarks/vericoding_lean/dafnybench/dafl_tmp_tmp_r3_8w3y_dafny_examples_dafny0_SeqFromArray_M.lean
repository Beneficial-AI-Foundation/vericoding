import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- M satisfies the following properties. -/
def M (a : Array Int) : Id Unit :=
  sorry

/-- Specification: M satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem M_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    M a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

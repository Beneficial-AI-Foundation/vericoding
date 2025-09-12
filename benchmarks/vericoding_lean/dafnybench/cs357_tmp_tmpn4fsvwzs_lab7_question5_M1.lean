import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- M1 satisfies the following properties. -/
def M1 (x : Int) : Id Unit :=
  sorry

/-- Specification: M1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem M1_spec (x : Int) :
    ⦃⌜True⌝⦄
    M1 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

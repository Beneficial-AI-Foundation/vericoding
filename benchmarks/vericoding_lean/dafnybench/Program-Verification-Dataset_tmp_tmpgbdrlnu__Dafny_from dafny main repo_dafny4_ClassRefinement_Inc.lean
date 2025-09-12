import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Get satisfies the following properties. -/
def Get (n : Int) : Id Unit :=
  sorry

/-- Specification: Get satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Get_spec (n : Int) :
    ⦃⌜True⌝⦄
    Get n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

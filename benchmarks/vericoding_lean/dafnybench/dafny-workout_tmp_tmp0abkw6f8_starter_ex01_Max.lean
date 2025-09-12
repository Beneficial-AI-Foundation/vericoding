import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Max satisfies the following properties. -/
def Max (a : Int) : Id Unit :=
  sorry

/-- Specification: Max satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Max_spec (a : Int) :
    ⦃⌜True⌝⦄
    Max a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

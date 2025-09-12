import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- LucidNumbers satisfies the following properties. -/
def LucidNumbers (n : Int) : Id Unit :=
  sorry

/-- Specification: LucidNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem LucidNumbers_spec (n : Int) :
    ⦃⌜True⌝⦄
    LucidNumbers n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

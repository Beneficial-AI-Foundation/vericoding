import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ZapNegatives satisfies the following properties. -/
def ZapNegatives (a : Array Int) : Id Unit :=
  sorry

/-- Specification: ZapNegatives satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ZapNegatives_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    ZapNegatives a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountEqualNumbers satisfies the following properties. -/
def CountEqualNumbers (a : Int) : Id Unit :=
  sorry

/-- Specification: CountEqualNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountEqualNumbers_spec (a : Int) :
    ⦃⌜True⌝⦄
    CountEqualNumbers a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

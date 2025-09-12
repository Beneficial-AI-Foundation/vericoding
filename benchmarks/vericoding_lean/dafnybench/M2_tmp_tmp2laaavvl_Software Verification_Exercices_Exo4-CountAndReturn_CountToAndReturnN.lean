import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountToAndReturnN satisfies the following properties. -/
def CountToAndReturnN (n : Int) : Id Unit :=
  sorry

/-- Specification: CountToAndReturnN satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountToAndReturnN_spec (n : Int) :
    ⦃⌜True⌝⦄
    CountToAndReturnN n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

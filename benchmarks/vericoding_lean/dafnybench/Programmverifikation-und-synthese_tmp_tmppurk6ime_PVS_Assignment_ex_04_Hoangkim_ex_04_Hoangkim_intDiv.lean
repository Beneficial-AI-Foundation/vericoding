import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- intDiv satisfies the following properties. -/
def intDiv (n : Int) : Id Unit :=
  sorry

/-- Specification: intDiv satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem intDiv_spec (n : Int) :
    ⦃⌜True⌝⦄
    intDiv n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

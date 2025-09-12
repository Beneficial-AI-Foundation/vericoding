import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- arraySum satisfies the following properties. -/
def arraySum (a : Array Int) : Id Unit :=
  sorry

/-- Specification: arraySum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem arraySum_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    arraySum a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

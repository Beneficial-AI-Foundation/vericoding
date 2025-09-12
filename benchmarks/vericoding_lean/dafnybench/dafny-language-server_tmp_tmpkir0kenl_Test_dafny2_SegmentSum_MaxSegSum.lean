import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MaxSegSum satisfies the following properties. -/
def MaxSegSum (a : List Int) : Id Unit :=
  sorry

/-- Specification: MaxSegSum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MaxSegSum_spec (a : List Int) :
    ⦃⌜True⌝⦄
    MaxSegSum a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

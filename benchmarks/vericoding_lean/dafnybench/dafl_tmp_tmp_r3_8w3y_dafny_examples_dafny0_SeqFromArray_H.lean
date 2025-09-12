import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- H satisfies the following properties. -/
def H (a : Array Int) : Id Unit :=
  sorry

/-- Specification: H satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem H_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    H a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

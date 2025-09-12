import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- exp_by_sqr satisfies the following properties. -/
def exp_by_sqr (x0 : Float) : Id Unit :=
  sorry

/-- Specification: exp_by_sqr satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem exp_by_sqr_spec (x0 : Float) :
    ⦃⌜True⌝⦄
    exp_by_sqr x0
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

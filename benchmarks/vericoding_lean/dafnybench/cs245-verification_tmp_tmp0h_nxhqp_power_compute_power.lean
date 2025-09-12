import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- compute_power satisfies the following properties. -/
def compute_power (a : Int) : Id Unit :=
  sorry

/-- Specification: compute_power satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem compute_power_spec (a : Int) :
    ⦃⌜True⌝⦄
    compute_power a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

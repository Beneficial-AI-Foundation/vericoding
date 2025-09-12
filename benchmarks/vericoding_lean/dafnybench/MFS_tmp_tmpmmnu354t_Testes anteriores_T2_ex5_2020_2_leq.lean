import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- leq satisfies the following properties. -/
def leq (a : Array Int) : Id Unit :=
  sorry

/-- Specification: leq satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem leq_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    leq a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

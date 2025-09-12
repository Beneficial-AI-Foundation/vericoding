import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- GCD1 satisfies the following properties. -/
def GCD1 (a : Int) : Id Unit :=
  sorry

/-- Specification: GCD1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem GCD1_spec (a : Int) :
    ⦃⌜True⌝⦄
    GCD1 a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

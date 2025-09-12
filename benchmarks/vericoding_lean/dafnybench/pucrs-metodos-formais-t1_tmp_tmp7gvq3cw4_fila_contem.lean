import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- contem satisfies the following properties. -/
def contem (e : Int) : Id Unit :=
  sorry

/-- Specification: contem satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem contem_spec (e : Int) :
    ⦃⌜True⌝⦄
    contem e
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

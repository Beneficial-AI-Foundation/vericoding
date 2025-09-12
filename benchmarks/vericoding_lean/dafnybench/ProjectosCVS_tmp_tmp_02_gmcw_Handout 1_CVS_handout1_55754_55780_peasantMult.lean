import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- peasantMult satisfies the following properties. -/
def peasantMult (a : Int) : Id Unit :=
  sorry

/-- Specification: peasantMult satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem peasantMult_spec (a : Int) :
    ⦃⌜True⌝⦄
    peasantMult a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Sqare2 satisfies the following properties. -/
def Sqare2 (a : Int) : Id Unit :=
  sorry

/-- Specification: Sqare2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Sqare2_spec (a : Int) :
    ⦃⌜True⌝⦄
    Sqare2 a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

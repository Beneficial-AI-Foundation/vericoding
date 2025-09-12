import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Sqare satisfies the following properties. -/
def Sqare (a : Int) : Id Unit :=
  sorry

/-- Specification: Sqare satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Sqare_spec (a : Int) :
    ⦃⌜True⌝⦄
    Sqare a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

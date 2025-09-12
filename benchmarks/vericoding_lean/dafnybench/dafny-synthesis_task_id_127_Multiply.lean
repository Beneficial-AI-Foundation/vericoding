import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Multiply satisfies the following properties. -/
def Multiply (a : Int) : Id Unit :=
  sorry

/-- Specification: Multiply satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Multiply_spec (a : Int) :
    ⦃⌜True⌝⦄
    Multiply a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

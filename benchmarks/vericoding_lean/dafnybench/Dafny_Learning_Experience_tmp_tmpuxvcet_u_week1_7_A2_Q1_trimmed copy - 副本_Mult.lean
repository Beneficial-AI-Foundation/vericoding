import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Mult satisfies the following properties. -/
def Mult (x : Int) : Id Unit :=
  sorry

/-- Specification: Mult satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Mult_spec (x : Int) :
    ⦃⌜True⌝⦄
    Mult x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

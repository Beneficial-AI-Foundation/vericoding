import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Abs satisfies the following properties. -/
def Abs (x : Int) : Id Unit :=
  sorry

/-- Specification: Abs satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Abs_spec (x : Int) :
    ⦃⌜True⌝⦄
    Abs x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

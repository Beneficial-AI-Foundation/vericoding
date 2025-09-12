import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumIntsLoop satisfies the following properties. -/
def SumIntsLoop (n : Int) : Id Unit :=
  sorry

/-- Specification: SumIntsLoop satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumIntsLoop_spec (n : Int) :
    ⦃⌜True⌝⦄
    SumIntsLoop n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

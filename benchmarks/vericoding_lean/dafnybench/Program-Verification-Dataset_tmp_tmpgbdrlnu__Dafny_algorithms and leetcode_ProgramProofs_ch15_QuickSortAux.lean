import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- QuickSortAux satisfies the following properties. -/
def QuickSortAux (a : Array Int) : Id Unit :=
  sorry

/-- Specification: QuickSortAux satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem QuickSortAux_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    QuickSortAux a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

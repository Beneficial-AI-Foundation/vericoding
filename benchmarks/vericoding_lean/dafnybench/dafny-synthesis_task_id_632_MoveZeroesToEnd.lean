import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MoveZeroesToEnd satisfies the following properties. -/
def MoveZeroesToEnd (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: MoveZeroesToEnd satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MoveZeroesToEnd_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    MoveZeroesToEnd arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ReverseUptoK satisfies the following properties. -/
def ReverseUptoK (s : Array Int) : Id Unit :=
  sorry

/-- Specification: ReverseUptoK satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ReverseUptoK_spec (s : Array Int) :
    ⦃⌜True⌝⦄
    ReverseUptoK s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

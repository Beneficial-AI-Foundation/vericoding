import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ArrayToSeq satisfies the following properties. -/
def ArrayToSeq (a : Array Int) : Id Unit :=
  sorry

/-- Specification: ArrayToSeq satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ArrayToSeq_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    ArrayToSeq a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

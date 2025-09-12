import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- maxSeq satisfies the following properties. -/
def maxSeq (v : List Int) : Id Unit :=
  sorry

/-- Specification: maxSeq satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem maxSeq_spec (v : List Int) :
    ⦃⌜True⌝⦄
    maxSeq v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

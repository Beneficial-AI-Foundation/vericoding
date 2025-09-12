import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- DeepCopySeq satisfies the following properties. -/
def DeepCopySeq (s : List Int) : Id Unit :=
  sorry

/-- Specification: DeepCopySeq satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem DeepCopySeq_spec (s : List Int) :
    ⦃⌜True⌝⦄
    DeepCopySeq s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

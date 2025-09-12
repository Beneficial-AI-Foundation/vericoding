import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SmallestMissingNumber satisfies the following properties. -/
def SmallestMissingNumber (s : List Int) : Id Unit :=
  sorry

/-- Specification: SmallestMissingNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SmallestMissingNumber_spec (s : List Int) :
    ⦃⌜True⌝⦄
    SmallestMissingNumber s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

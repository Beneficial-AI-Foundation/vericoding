import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountArrays satisfies the following properties. -/
def CountArrays (arrays : seq<array<int>>) : Id Unit :=
  sorry

/-- Specification: CountArrays satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountArrays_spec (arrays : seq<array<int>>) :
    ⦃⌜True⌝⦄
    CountArrays arrays
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

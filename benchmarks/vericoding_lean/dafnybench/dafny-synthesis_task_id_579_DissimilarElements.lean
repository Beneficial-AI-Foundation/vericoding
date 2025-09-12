import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- DissimilarElements satisfies the following properties. -/
def DissimilarElements (a : Array Int) : Id Unit :=
  sorry

/-- Specification: DissimilarElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem DissimilarElements_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    DissimilarElements a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

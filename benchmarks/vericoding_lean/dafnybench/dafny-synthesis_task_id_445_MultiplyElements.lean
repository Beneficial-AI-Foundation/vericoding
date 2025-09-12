import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MultiplyElements satisfies the following properties. -/
def MultiplyElements (a : List Int) : Id Unit :=
  sorry

/-- Specification: MultiplyElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MultiplyElements_spec (a : List Int) :
    ⦃⌜True⌝⦄
    MultiplyElements a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

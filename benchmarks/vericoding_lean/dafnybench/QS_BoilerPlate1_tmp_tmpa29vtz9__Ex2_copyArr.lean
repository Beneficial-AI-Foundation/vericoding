import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sorted satisfies the following properties. -/
def sorted (s : List Int) : Id Unit :=
  sorry

/-- Specification: sorted satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sorted_spec (s : List Int) :
    ⦃⌜True⌝⦄
    sorted s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ContainsK satisfies the following properties. -/
def ContainsK (s : List Int) : Id Unit :=
  sorry

/-- Specification: ContainsK satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ContainsK_spec (s : List Int) :
    ⦃⌜True⌝⦄
    ContainsK s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

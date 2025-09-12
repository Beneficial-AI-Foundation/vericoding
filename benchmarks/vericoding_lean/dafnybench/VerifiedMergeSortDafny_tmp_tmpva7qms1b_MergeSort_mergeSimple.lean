import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mergeSimple satisfies the following properties. -/
def mergeSimple (a1 : List Int) : Id Unit :=
  sorry

/-- Specification: mergeSimple satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mergeSimple_spec (a1 : List Int) :
    ⦃⌜True⌝⦄
    mergeSimple a1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

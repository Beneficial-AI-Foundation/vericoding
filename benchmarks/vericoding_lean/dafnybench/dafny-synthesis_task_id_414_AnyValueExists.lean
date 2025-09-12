import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AnyValueExists satisfies the following properties. -/
def AnyValueExists (seq1 : List Int) : Id Unit :=
  sorry

/-- Specification: AnyValueExists satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AnyValueExists_spec (seq1 : List Int) :
    ⦃⌜True⌝⦄
    AnyValueExists seq1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

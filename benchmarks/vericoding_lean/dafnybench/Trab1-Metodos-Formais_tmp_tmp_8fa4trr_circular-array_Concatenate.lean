import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AsSequence satisfies the following properties. -/
def AsSequence (s : List Int) : Id Unit :=
  sorry

/-- Specification: AsSequence satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AsSequence_spec (s : List Int) :
    ⦃⌜True⌝⦄
    AsSequence s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

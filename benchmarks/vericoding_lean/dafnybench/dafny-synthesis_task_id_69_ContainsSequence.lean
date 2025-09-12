import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ContainsSequence satisfies the following properties. -/
def ContainsSequence (list : seq<seq<int>>) : Id Unit :=
  sorry

/-- Specification: ContainsSequence satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ContainsSequence_spec (list : seq<seq<int>>) :
    ⦃⌜True⌝⦄
    ContainsSequence list
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

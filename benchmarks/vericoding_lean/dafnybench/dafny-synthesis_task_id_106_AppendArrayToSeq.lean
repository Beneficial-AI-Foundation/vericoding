import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AppendArrayToSeq satisfies the following properties. -/
def AppendArrayToSeq (s : List Int) : Id Unit :=
  sorry

/-- Specification: AppendArrayToSeq satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AppendArrayToSeq_spec (s : List Int) :
    ⦃⌜True⌝⦄
    AppendArrayToSeq s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

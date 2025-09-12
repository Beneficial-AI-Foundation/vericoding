import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ExtractRearChars satisfies the following properties. -/
def ExtractRearChars (l : seq<string>) : Id Unit :=
  sorry

/-- Specification: ExtractRearChars satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ExtractRearChars_spec (l : seq<string>) :
    ⦃⌜True⌝⦄
    ExtractRearChars l
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MaxLengthList satisfies the following properties. -/
def MaxLengthList (lists : seq<seq<int>>) : Id Unit :=
  sorry

/-- Specification: MaxLengthList satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MaxLengthList_spec (lists : seq<seq<int>>) :
    ⦃⌜True⌝⦄
    MaxLengthList lists
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

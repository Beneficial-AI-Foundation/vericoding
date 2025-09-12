import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SmallestListLength satisfies the following properties. -/
def SmallestListLength (s : seq<seq<int>>) : Id Unit :=
  sorry

/-- Specification: SmallestListLength satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SmallestListLength_spec (s : seq<seq<int>>) :
    ⦃⌜True⌝⦄
    SmallestListLength s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

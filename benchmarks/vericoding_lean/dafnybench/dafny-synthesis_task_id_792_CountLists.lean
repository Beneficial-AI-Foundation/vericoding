import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountLists satisfies the following properties. -/
def CountLists (lists : seq<seq<int>>) : Id Unit :=
  sorry

/-- Specification: CountLists satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountLists_spec (lists : seq<seq<int>>) :
    ⦃⌜True⌝⦄
    CountLists lists
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

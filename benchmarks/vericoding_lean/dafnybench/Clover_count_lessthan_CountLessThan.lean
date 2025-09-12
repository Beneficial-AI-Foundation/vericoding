import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountLessThan satisfies the following properties. -/
def CountLessThan (numbers : set<int>) : Id Unit :=
  sorry

/-- Specification: CountLessThan satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountLessThan_spec (numbers : set<int>) :
    ⦃⌜True⌝⦄
    CountLessThan numbers
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- TwoSum satisfies the following properties. -/
def TwoSum (nums : Array Int) : Id Unit :=
  sorry

/-- Specification: TwoSum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem TwoSum_spec (nums : Array Int) :
    ⦃⌜True⌝⦄
    TwoSum nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

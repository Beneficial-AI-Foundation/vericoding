import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- twoSum satisfies the following properties. -/
def twoSum (nums : Array Int) : Id Unit :=
  sorry

/-- Specification: twoSum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem twoSum_spec (nums : Array Int) :
    ⦃⌜True⌝⦄
    twoSum nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

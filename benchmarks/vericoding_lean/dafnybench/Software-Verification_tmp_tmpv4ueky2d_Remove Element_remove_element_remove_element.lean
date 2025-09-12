import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- remove_element satisfies the following properties. -/
def remove_element (nums : Array Int) : Id Unit :=
  sorry

/-- Specification: remove_element satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem remove_element_spec (nums : Array Int) :
    ⦃⌜True⌝⦄
    remove_element nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

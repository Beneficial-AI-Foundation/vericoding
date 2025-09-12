import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- double_array_elements satisfies the following properties. -/
def double_array_elements (s : Array Int) : Id Unit :=
  sorry

/-- Specification: double_array_elements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem double_array_elements_spec (s : Array Int) :
    ⦃⌜True⌝⦄
    double_array_elements s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

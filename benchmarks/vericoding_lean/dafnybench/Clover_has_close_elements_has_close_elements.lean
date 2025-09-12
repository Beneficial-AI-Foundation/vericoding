import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- has_close_elements satisfies the following properties. -/
def has_close_elements (numbers : seq<real>) : Id Unit :=
  sorry

/-- Specification: has_close_elements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem has_close_elements_spec (numbers : seq<real>) :
    ⦃⌜True⌝⦄
    has_close_elements numbers
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

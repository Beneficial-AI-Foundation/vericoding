import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- replace satisfies the following properties. -/
def replace (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: replace satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem replace_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    replace arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

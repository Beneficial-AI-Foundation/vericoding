import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- replace satisfies the following properties. -/
def replace (v : Array Int) : Id Unit :=
  sorry

/-- Specification: replace satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem replace_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    replace v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- reverse satisfies the following properties. -/
def reverse (a : Array Int) : Id Unit :=
  sorry

/-- Specification: reverse satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem reverse_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    reverse a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

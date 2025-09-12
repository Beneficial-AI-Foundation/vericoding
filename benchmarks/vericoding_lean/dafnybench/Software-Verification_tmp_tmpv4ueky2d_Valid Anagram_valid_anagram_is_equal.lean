import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- is_equal satisfies the following properties. -/
def is_equal (s : multiset<char>) : Id Unit :=
  sorry

/-- Specification: is_equal satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem is_equal_spec (s : multiset<char>) :
    ⦃⌜True⌝⦄
    is_equal s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

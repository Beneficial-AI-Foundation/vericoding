import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- longestPrefix satisfies the following properties. -/
def longestPrefix (a : Array Int) : Id Unit :=
  sorry

/-- Specification: longestPrefix satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem longestPrefix_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    longestPrefix a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

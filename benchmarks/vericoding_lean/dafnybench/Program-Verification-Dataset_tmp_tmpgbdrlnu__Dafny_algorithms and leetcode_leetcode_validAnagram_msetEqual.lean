import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- msetEqual satisfies the following properties. -/
def msetEqual (s : multiset<char>) : Id Unit :=
  sorry

/-- Specification: msetEqual satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem msetEqual_spec (s : multiset<char>) :
    ⦃⌜True⌝⦄
    msetEqual s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

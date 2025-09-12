import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AbsIt satisfies the following properties. -/
def AbsIt (s : Array Int) : Id Unit :=
  sorry

/-- Specification: AbsIt satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AbsIt_spec (s : Array Int) :
    ⦃⌜True⌝⦄
    AbsIt s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

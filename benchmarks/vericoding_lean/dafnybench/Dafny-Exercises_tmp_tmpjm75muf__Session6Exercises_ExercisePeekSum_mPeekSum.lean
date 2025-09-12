import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mPeekSum satisfies the following properties. -/
def mPeekSum (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mPeekSum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mPeekSum_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mPeekSum v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

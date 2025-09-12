import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mcontained satisfies the following properties. -/
def mcontained (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mcontained satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mcontained_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mcontained v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

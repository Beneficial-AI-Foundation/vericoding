import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mpositive satisfies the following properties. -/
def mpositive (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mpositive satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mpositive_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mpositive v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

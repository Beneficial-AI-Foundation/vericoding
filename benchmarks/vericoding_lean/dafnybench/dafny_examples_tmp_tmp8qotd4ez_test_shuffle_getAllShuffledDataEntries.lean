import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- random satisfies the following properties. -/
def random (a : Int) : Id Unit :=
  sorry

/-- Specification: random satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem random_spec (a : Int) :
    ⦃⌜True⌝⦄
    random a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

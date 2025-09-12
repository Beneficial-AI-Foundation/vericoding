import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- simple satisfies the following properties. -/
def simple (y : Int) : Id Unit :=
  sorry

/-- Specification: simple satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem simple_spec (y : Int) :
    ⦃⌜True⌝⦄
    simple y
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

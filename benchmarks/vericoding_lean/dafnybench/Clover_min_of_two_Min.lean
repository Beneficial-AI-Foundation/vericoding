import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Min satisfies the following properties. -/
def Min (x : Int) : Id Unit :=
  sorry

/-- Specification: Min satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Min_spec (x : Int) :
    ⦃⌜True⌝⦄
    Min x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

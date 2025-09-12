import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Min satisfies the following properties. -/
def Min (a : Int) : Id Unit :=
  sorry

/-- Specification: Min satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Min_spec (a : Int) :
    ⦃⌜True⌝⦄
    Min a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

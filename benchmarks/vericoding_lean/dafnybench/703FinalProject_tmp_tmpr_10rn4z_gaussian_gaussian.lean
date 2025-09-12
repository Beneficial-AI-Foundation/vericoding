import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- gaussian satisfies the following properties. -/
def gaussian (size : Int) : Id Unit :=
  sorry

/-- Specification: gaussian satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem gaussian_spec (size : Int) :
    ⦃⌜True⌝⦄
    gaussian size
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

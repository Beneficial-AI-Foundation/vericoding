import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Gauss satisfies the following properties. -/
def Gauss (n : Int) : Id Unit :=
  sorry

/-- Specification: Gauss satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Gauss_spec (n : Int) :
    ⦃⌜True⌝⦄
    Gauss n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

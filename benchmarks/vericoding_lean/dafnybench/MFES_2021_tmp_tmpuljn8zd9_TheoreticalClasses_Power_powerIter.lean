import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- powerIter satisfies the following properties. -/
def powerIter (x : Float) : Id Unit :=
  sorry

/-- Specification: powerIter satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem powerIter_spec (x : Float) :
    ⦃⌜True⌝⦄
    powerIter x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- nonZeroReturn satisfies the following properties. -/
def nonZeroReturn (x : Int) : Id Unit :=
  sorry

/-- Specification: nonZeroReturn satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem nonZeroReturn_spec (x : Int) :
    ⦃⌜True⌝⦄
    nonZeroReturn x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

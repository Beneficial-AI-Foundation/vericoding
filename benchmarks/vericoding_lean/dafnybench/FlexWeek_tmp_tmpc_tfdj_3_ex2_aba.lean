import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- abs satisfies the following properties. -/
def abs (a : Int) : Id Unit :=
  sorry

/-- Specification: abs satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem abs_spec (a : Int) :
    ⦃⌜True⌝⦄
    abs a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

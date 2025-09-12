import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- expt satisfies the following properties. -/
def expt (b : Int) : Id Unit :=
  sorry

/-- Specification: expt satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem expt_spec (b : Int) :
    ⦃⌜True⌝⦄
    expt b
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

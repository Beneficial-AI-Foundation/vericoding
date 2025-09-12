import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Allow42 satisfies the following properties. -/
def Allow42 (x : Int) : Id Unit :=
  sorry

/-- Specification: Allow42 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Allow42_spec (x : Int) :
    ⦃⌜True⌝⦄
    Allow42 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

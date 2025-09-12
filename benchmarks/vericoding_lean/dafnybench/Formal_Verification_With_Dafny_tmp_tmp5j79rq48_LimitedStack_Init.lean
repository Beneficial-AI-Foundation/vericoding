import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Init satisfies the following properties. -/
def Init (c : Int) : Id Unit :=
  sorry

/-- Specification: Init satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Init_spec (c : Int) :
    ⦃⌜True⌝⦄
    Init c
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

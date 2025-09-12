import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Init satisfies the following properties. -/
def Init (x : Int) : Id Unit :=
  sorry

/-- Specification: Init satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Init_spec (x : Int) :
    ⦃⌜True⌝⦄
    Init x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

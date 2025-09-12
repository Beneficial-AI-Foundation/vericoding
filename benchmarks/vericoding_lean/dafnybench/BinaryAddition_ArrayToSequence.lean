import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BoolToInt satisfies the following properties. -/
def BoolToInt (a : Bool) : Id Unit :=
  sorry

/-- Specification: BoolToInt satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BoolToInt_spec (a : Bool) :
    ⦃⌜True⌝⦄
    BoolToInt a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

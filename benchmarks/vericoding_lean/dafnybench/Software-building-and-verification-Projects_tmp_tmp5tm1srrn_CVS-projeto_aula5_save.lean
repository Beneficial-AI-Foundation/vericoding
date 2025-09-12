import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- save satisfies the following properties. -/
def save (amount : Int) : Id Unit :=
  sorry

/-- Specification: save satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem save_spec (amount : Int) :
    ⦃⌜True⌝⦄
    save amount
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

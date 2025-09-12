import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Front satisfies the following properties. -/
def Front (x : Int) : Id Unit :=
  sorry

/-- Specification: Front satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Front_spec (x : Int) :
    ⦃⌜True⌝⦄
    Front x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

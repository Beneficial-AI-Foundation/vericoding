import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- isEmpty satisfies the following properties. -/
def isEmpty (res : Bool) : Id Unit :=
  sorry

/-- Specification: isEmpty satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem isEmpty_spec (res : Bool) :
    ⦃⌜True⌝⦄
    isEmpty res
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

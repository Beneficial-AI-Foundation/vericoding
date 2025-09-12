import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Prepend satisfies the following properties. -/
def Prepend (d : T) : Id Unit :=
  sorry

/-- Specification: Prepend satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Prepend_spec (d : T) :
    ⦃⌜True⌝⦄
    Prepend d
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

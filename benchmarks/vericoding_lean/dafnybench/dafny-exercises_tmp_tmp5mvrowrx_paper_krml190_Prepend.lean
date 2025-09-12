import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Prepend satisfies the following properties. -/
def Prepend (d : Data) : Id Unit :=
  sorry

/-- Specification: Prepend satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Prepend_spec (d : Data) :
    ⦃⌜True⌝⦄
    Prepend d
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

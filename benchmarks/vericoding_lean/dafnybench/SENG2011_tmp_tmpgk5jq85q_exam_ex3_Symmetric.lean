import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Symmetric satisfies the following properties. -/
def Symmetric (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Symmetric satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Symmetric_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Symmetric a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

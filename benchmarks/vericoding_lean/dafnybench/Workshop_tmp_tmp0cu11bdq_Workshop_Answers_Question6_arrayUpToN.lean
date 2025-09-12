import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- arrayUpToN satisfies the following properties. -/
def arrayUpToN (n : Int) : Id Unit :=
  sorry

/-- Specification: arrayUpToN satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem arrayUpToN_spec (n : Int) :
    ⦃⌜True⌝⦄
    arrayUpToN n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- m2 satisfies the following properties. -/
def m2 (x : Nat) : Id Unit :=
  sorry

/-- Specification: m2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem m2_spec (x : Nat) :
    ⦃⌜True⌝⦄
    m2 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

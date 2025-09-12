import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ComputeFib satisfies the following properties. -/
def ComputeFib (n : Nat) : Id Unit :=
  sorry

/-- Specification: ComputeFib satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ComputeFib_spec (n : Nat) :
    ⦃⌜True⌝⦄
    ComputeFib n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

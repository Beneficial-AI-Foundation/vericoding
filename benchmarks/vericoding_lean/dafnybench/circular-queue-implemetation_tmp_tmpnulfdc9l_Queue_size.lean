import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- size satisfies the following properties. -/
def size (size : Nat) : Id Unit :=
  sorry

/-- Specification: size satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem size_spec (size : Nat) :
    ⦃⌜True⌝⦄
    size size
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

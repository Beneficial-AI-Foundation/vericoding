import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SquareRoot satisfies the following properties. -/
def SquareRoot (N : Nat) : Id Unit :=
  sorry

/-- Specification: SquareRoot satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SquareRoot_spec (N : Nat) :
    ⦃⌜True⌝⦄
    SquareRoot N
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

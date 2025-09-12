import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- max_nit satisfies the following properties. -/
def max_nit (b : Nat) : Id Unit :=
  sorry

/-- Specification: max_nit satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem max_nit_spec (b : Nat) :
    ⦃⌜True⌝⦄
    max_nit b
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

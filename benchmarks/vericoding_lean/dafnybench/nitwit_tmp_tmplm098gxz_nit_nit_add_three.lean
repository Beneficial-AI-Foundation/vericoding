import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- nit_add satisfies the following properties. -/
def nit_add (b : Nat) : Id Unit :=
  sorry

/-- Specification: nit_add satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem nit_add_spec (b : Nat) :
    ⦃⌜True⌝⦄
    nit_add b
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

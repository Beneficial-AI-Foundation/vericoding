import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- nit_increment satisfies the following properties. -/
def nit_increment (b : Nat) : Id Unit :=
  sorry

/-- Specification: nit_increment satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem nit_increment_spec (b : Nat) :
    ⦃⌜True⌝⦄
    nit_increment b
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

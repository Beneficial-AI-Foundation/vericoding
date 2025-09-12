import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Comb satisfies the following properties. -/
def Comb (n : Nat) : Id Unit :=
  sorry

/-- Specification: Comb satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Comb_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Comb n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

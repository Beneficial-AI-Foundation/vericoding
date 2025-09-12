import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sumOdds satisfies the following properties. -/
def sumOdds (n : Nat) : Id Unit :=
  sorry

/-- Specification: sumOdds satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sumOdds_spec (n : Nat) :
    ⦃⌜True⌝⦄
    sumOdds n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

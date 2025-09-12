import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CalculationalStyleProof satisfies the following properties. -/
def CalculationalStyleProof (a : Int) : Id Unit :=
  sorry

/-- Specification: CalculationalStyleProof satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CalculationalStyleProof_spec (a : Int) :
    ⦃⌜True⌝⦄
    CalculationalStyleProof a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

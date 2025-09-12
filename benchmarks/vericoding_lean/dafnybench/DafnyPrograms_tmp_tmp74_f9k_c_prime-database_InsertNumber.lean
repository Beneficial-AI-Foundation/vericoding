import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- testPrimeness satisfies the following properties. -/
def testPrimeness (n : Nat) : Id Unit :=
  sorry

/-- Specification: testPrimeness satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem testPrimeness_spec (n : Nat) :
    ⦃⌜True⌝⦄
    testPrimeness n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

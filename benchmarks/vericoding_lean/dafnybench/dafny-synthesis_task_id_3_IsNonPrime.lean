import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsNonPrime satisfies the following properties. -/
def IsNonPrime (n : Int) : Id Unit :=
  sorry

/-- Specification: IsNonPrime satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsNonPrime_spec (n : Int) :
    ⦃⌜True⌝⦄
    IsNonPrime n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

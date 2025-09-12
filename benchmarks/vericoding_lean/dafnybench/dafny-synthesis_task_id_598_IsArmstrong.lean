import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsArmstrong satisfies the following properties. -/
def IsArmstrong (n : Int) : Id Unit :=
  sorry

/-- Specification: IsArmstrong satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsArmstrong_spec (n : Int) :
    ⦃⌜True⌝⦄
    IsArmstrong n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

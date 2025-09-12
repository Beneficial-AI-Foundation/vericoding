import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- pow satisfies the following properties. -/
def pow (n : Nat) : Id Unit :=
  sorry

/-- Specification: pow satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem pow_spec (n : Nat) :
    ⦃⌜True⌝⦄
    pow n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

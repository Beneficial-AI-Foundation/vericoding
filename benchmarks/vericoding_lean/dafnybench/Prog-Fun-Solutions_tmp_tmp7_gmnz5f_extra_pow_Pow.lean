import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- pow satisfies the following properties. -/
def pow (a : Int) : Id Unit :=
  sorry

/-- Specification: pow satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem pow_spec (a : Int) :
    ⦃⌜True⌝⦄
    pow a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

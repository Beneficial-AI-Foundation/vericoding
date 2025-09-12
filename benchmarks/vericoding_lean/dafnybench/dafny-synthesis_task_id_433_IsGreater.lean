import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsGreater satisfies the following properties. -/
def IsGreater (n : Int) : Id Unit :=
  sorry

/-- Specification: IsGreater satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsGreater_spec (n : Int) :
    ⦃⌜True⌝⦄
    IsGreater n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

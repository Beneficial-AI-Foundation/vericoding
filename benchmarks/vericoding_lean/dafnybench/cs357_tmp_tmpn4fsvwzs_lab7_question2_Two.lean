import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Two satisfies the following properties. -/
def Two (x : Int) : Id Unit :=
  sorry

/-- Specification: Two satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Two_spec (x : Int) :
    ⦃⌜True⌝⦄
    Two x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

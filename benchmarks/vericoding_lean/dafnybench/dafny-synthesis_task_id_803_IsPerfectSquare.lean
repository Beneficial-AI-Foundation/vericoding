import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsPerfectSquare satisfies the following properties. -/
def IsPerfectSquare (n : Int) : Id Unit :=
  sorry

/-- Specification: IsPerfectSquare satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsPerfectSquare_spec (n : Int) :
    ⦃⌜True⌝⦄
    IsPerfectSquare n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

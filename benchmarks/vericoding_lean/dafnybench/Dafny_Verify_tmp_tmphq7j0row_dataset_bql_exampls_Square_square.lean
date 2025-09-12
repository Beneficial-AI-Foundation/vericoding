import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- square satisfies the following properties. -/
def square (n : Int) : Id Unit :=
  sorry

/-- Specification: square satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem square_spec (n : Int) :
    ⦃⌜True⌝⦄
    square n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- is_even satisfies the following properties. -/
def is_even (n : Int) : Id Unit :=
  sorry

/-- Specification: is_even satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem is_even_spec (n : Int) :
    ⦃⌜True⌝⦄
    is_even n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

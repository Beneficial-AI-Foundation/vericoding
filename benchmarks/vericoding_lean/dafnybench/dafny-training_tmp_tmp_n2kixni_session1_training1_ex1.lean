import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ex1 satisfies the following properties. -/
def ex1 (n : Int) : Id Unit :=
  sorry

/-- Specification: ex1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ex1_spec (n : Int) :
    ⦃⌜True⌝⦄
    ex1 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

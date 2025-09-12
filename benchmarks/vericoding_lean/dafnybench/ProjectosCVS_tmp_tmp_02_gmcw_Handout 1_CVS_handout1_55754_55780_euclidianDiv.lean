import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- euclidianDiv satisfies the following properties. -/
def euclidianDiv (a : Int) : Id Unit :=
  sorry

/-- Specification: euclidianDiv satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem euclidianDiv_spec (a : Int) :
    ⦃⌜True⌝⦄
    euclidianDiv a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

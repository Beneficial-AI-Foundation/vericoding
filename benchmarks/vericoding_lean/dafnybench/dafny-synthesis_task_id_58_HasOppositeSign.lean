import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- HasOppositeSign satisfies the following properties. -/
def HasOppositeSign (a : Int) : Id Unit :=
  sorry

/-- Specification: HasOppositeSign satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem HasOppositeSign_spec (a : Int) :
    ⦃⌜True⌝⦄
    HasOppositeSign a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

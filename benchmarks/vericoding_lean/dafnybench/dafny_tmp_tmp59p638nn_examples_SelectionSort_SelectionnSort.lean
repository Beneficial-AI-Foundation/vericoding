import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SelectionnSort satisfies the following properties. -/
def SelectionnSort (a : Array Int) : Id Unit :=
  sorry

/-- Specification: SelectionnSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SelectionnSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    SelectionnSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

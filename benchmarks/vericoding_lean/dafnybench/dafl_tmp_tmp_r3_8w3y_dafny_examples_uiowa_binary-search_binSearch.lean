import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- binSearch satisfies the following properties. -/
def binSearch (a : Array Int) : Id Unit :=
  sorry

/-- Specification: binSearch satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem binSearch_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    binSearch a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

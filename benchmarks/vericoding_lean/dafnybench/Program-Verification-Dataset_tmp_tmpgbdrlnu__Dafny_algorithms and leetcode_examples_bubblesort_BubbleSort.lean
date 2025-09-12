import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- NChoose2 satisfies the following properties. -/
def NChoose2 (n : Int) : Id Unit :=
  sorry

/-- Specification: NChoose2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem NChoose2_spec (n : Int) :
    ⦃⌜True⌝⦄
    NChoose2 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

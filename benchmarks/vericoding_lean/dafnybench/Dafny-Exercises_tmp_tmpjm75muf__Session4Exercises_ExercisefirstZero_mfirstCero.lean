import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mfirstCero satisfies the following properties. -/
def mfirstCero (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mfirstCero satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mfirstCero_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mfirstCero v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

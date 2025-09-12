import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mfirstMaximum satisfies the following properties. -/
def mfirstMaximum (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mfirstMaximum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mfirstMaximum_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mfirstMaximum v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

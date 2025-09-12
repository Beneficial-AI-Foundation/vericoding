import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mCountMin satisfies the following properties. -/
def mCountMin (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mCountMin satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mCountMin_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mCountMin v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

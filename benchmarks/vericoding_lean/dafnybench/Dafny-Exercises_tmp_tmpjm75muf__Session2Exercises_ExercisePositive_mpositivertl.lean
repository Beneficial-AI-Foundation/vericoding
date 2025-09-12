import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mpositivertl satisfies the following properties. -/
def mpositivertl (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mpositivertl satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mpositivertl_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mpositivertl v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

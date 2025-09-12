import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- getValue satisfies the following properties. -/
def getValue (x : Int) : Id Unit :=
  sorry

/-- Specification: getValue satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem getValue_spec (x : Int) :
    ⦃⌜True⌝⦄
    getValue x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

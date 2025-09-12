import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- bar satisfies the following properties. -/
def bar (x : Int) : Id Unit :=
  sorry

/-- Specification: bar satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem bar_spec (x : Int) :
    ⦃⌜True⌝⦄
    bar x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

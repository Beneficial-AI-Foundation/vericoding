import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MaxSum satisfies the following properties. -/
def MaxSum (x : Int) : Id Unit :=
  sorry

/-- Specification: MaxSum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MaxSum_spec (x : Int) :
    ⦃⌜True⌝⦄
    MaxSum x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

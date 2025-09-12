import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mySqrt satisfies the following properties. -/
def mySqrt (x : Int) : Id Unit :=
  sorry

/-- Specification: mySqrt satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mySqrt_spec (x : Int) :
    ⦃⌜True⌝⦄
    mySqrt x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

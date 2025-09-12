import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ReverseInPlace satisfies the following properties. -/
def ReverseInPlace (x : Node?) : Id Unit :=
  sorry

/-- Specification: ReverseInPlace satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ReverseInPlace_spec (x : Node?) :
    ⦃⌜True⌝⦄
    ReverseInPlace x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ReverseInPlace satisfies the following properties. -/
def ReverseInPlace (reverse : Node) : Id Unit :=
  sorry

/-- Specification: ReverseInPlace satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ReverseInPlace_spec (reverse : Node) :
    ⦃⌜True⌝⦄
    ReverseInPlace reverse
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

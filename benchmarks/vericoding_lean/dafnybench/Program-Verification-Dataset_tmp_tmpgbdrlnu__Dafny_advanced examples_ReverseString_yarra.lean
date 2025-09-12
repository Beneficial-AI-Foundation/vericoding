import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- yarra satisfies the following properties. -/
def yarra (arr : array<char>) : Id Unit :=
  sorry

/-- Specification: yarra satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem yarra_spec (arr : array<char>) :
    ⦃⌜True⌝⦄
    yarra arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

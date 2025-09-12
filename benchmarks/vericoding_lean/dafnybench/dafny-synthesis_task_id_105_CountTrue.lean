import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountTrue satisfies the following properties. -/
def CountTrue (a : array<bool>) : Id Unit :=
  sorry

/-- Specification: CountTrue satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountTrue_spec (a : array<bool>) :
    ⦃⌜True⌝⦄
    CountTrue a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

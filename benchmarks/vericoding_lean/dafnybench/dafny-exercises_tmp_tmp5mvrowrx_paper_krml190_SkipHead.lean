import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SkipHead satisfies the following properties. -/
def SkipHead (r : Node?) : Id Unit :=
  sorry

/-- Specification: SkipHead satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SkipHead_spec (r : Node?) :
    ⦃⌜True⌝⦄
    SkipHead r
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SkipHead satisfies the following properties. -/
def SkipHead (r : Node?<T>) : Id Unit :=
  sorry

/-- Specification: SkipHead satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SkipHead_spec (r : Node?<T>) :
    ⦃⌜True⌝⦄
    SkipHead r
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

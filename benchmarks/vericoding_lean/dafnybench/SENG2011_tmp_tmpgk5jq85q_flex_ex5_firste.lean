import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- firste satisfies the following properties. -/
def firste (a : array<char>) : Id Unit :=
  sorry

/-- Specification: firste satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem firste_spec (a : array<char>) :
    ⦃⌜True⌝⦄
    firste a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

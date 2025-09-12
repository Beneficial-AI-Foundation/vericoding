import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Deli satisfies the following properties. -/
def Deli (a : array<char>) : Id Unit :=
  sorry

/-- Specification: Deli satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Deli_spec (a : array<char>) :
    ⦃⌜True⌝⦄
    Deli a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

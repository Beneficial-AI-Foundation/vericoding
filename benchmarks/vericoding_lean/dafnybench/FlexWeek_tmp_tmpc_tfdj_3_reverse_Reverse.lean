import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Reverse satisfies the following properties. -/
def Reverse (a : array<char>) : Id Unit :=
  sorry

/-- Specification: Reverse satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Reverse_spec (a : array<char>) :
    ⦃⌜True⌝⦄
    Reverse a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

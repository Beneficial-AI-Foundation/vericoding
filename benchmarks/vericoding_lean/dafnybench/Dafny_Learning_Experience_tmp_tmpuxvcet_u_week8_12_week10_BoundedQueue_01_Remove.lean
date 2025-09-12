import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Remove satisfies the following properties. -/
def Remove (x : T) : Id Unit :=
  sorry

/-- Specification: Remove satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Remove_spec (x : T) :
    ⦃⌜True⌝⦄
    Remove x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- add_by_inc satisfies the following properties. -/
def add_by_inc (x : Nat) : Id Unit :=
  sorry

/-- Specification: add_by_inc satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem add_by_inc_spec (x : Nat) :
    ⦃⌜True⌝⦄
    add_by_inc x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

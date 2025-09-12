import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- add_small_numbers satisfies the following properties. -/
def add_small_numbers (a : Array Int) : Id Unit :=
  sorry

/-- Specification: add_small_numbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem add_small_numbers_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    add_small_numbers a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

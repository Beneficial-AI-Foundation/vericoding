import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- add_by_one satisfies the following properties. -/
def add_by_one (x : Int) : Id Unit :=
  sorry

/-- Specification: add_by_one satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem add_by_one_spec (x : Int) :
    ⦃⌜True⌝⦄
    add_by_one x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

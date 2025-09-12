import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- add satisfies the following properties. -/
def add (v : Int) : Id Unit :=
  sorry

/-- Specification: add satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem add_spec (v : Int) :
    ⦃⌜True⌝⦄
    add v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

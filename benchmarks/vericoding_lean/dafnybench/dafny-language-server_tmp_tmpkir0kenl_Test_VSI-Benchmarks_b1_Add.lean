import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Add satisfies the following properties. -/
def Add (x : Int) : Id Unit :=
  sorry

/-- Specification: Add satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Add_spec (x : Int) :
    ⦃⌜True⌝⦄
    Add x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

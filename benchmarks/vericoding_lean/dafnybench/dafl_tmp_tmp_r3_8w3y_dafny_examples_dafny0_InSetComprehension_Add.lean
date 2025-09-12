import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Add satisfies the following properties. -/
def Add (t : T) : Id Unit :=
  sorry

/-- Specification: Add satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Add_spec (t : T) :
    ⦃⌜True⌝⦄
    Add t
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

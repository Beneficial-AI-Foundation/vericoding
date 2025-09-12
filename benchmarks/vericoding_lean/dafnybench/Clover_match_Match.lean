import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Match satisfies the following properties. -/
def Match (s : String) : Id Unit :=
  sorry

/-- Specification: Match satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Match_spec (s : String) :
    ⦃⌜True⌝⦄
    Match s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

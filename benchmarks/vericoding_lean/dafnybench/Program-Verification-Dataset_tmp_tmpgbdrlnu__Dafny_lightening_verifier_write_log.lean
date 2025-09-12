import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- countdown satisfies the following properties. -/
def countdown (s : GhostState) : Id Unit :=
  sorry

/-- Specification: countdown satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem countdown_spec (s : GhostState) :
    ⦃⌜True⌝⦄
    countdown s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

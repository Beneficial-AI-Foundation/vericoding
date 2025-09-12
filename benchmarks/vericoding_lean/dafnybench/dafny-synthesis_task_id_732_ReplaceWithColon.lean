import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ReplaceWithColon satisfies the following properties. -/
def ReplaceWithColon (s : String) : Id Unit :=
  sorry

/-- Specification: ReplaceWithColon satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ReplaceWithColon_spec (s : String) :
    ⦃⌜True⌝⦄
    ReplaceWithColon s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

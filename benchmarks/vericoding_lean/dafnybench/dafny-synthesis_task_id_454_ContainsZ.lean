import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ContainsZ satisfies the following properties. -/
def ContainsZ (s : String) : Id Unit :=
  sorry

/-- Specification: ContainsZ satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ContainsZ_spec (s : String) :
    ⦃⌜True⌝⦄
    ContainsZ s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

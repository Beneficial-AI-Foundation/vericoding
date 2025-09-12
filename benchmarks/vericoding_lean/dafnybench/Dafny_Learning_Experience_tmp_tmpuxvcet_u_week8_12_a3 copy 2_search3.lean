import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- search3 satisfies the following properties. -/
def search3 (Element : T) : Id Unit :=
  sorry

/-- Specification: search3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem search3_spec (Element : T) :
    ⦃⌜True⌝⦄
    search3 Element
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

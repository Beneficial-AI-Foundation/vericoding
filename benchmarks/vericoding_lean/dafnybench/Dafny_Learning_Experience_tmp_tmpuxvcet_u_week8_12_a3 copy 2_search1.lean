import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- search1 satisfies the following properties. -/
def search1 (Element : T) : Id Unit :=
  sorry

/-- Specification: search1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem search1_spec (Element : T) :
    ⦃⌜True⌝⦄
    search1 Element
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

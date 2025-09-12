import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- queryFast satisfies the following properties. -/
def queryFast (a : Array Int) : Id Unit :=
  sorry

/-- Specification: queryFast satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem queryFast_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    queryFast a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

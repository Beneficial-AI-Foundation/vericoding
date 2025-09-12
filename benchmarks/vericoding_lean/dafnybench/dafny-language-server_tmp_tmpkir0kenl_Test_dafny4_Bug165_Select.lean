import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Select satisfies the following properties. -/
def Select (s1 : List T) : Id Unit :=
  sorry

/-- Specification: Select satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Select_spec (s1 : List T) :
    ⦃⌜True⌝⦄
    Select s1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

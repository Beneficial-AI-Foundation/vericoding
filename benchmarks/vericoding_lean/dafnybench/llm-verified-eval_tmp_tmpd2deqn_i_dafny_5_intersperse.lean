import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- intersperse satisfies the following properties. -/
def intersperse (numbers : List Int) : Id Unit :=
  sorry

/-- Specification: intersperse satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem intersperse_spec (numbers : List Int) :
    ⦃⌜True⌝⦄
    intersperse numbers
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

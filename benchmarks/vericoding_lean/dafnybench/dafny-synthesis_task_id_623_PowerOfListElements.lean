import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- PowerOfListElements satisfies the following properties. -/
def PowerOfListElements (l : List Int) : Id Unit :=
  sorry

/-- Specification: PowerOfListElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem PowerOfListElements_spec (l : List Int) :
    ⦃⌜True⌝⦄
    PowerOfListElements l
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

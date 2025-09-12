import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsLetter satisfies the following properties. -/
def IsLetter (c : char) : Id Unit :=
  sorry

/-- Specification: IsLetter satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsLetter_spec (c : char) :
    ⦃⌜True⌝⦄
    IsLetter c
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

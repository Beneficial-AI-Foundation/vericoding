import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsSublist satisfies the following properties. -/
def IsSublist (sub : List Int) : Id Unit :=
  sorry

/-- Specification: IsSublist satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsSublist_spec (sub : List Int) :
    ⦃⌜True⌝⦄
    IsSublist sub
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsEvenAtIndexEven satisfies the following properties. -/
def IsEvenAtIndexEven (lst : List Int) : Id Unit :=
  sorry

/-- Specification: IsEvenAtIndexEven satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsEvenAtIndexEven_spec (lst : List Int) :
    ⦃⌜True⌝⦄
    IsEvenAtIndexEven lst
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

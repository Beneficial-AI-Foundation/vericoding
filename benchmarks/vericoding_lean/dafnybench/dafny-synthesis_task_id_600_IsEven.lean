import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsEven satisfies the following properties. -/
def IsEven (n : Int) : Id Unit :=
  sorry

/-- Specification: IsEven satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsEven_spec (n : Int) :
    ⦃⌜True⌝⦄
    IsEven n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

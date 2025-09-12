import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsProductEven satisfies the following properties. -/
def IsProductEven (a : Array Int) : Id Unit :=
  sorry

/-- Specification: IsProductEven satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsProductEven_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    IsProductEven a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ToCharArray satisfies the following properties. -/
def ToCharArray (s : String) : Id Unit :=
  sorry

/-- Specification: ToCharArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ToCharArray_spec (s : String) :
    ⦃⌜True⌝⦄
    ToCharArray s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

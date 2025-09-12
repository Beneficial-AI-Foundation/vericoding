import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- StarNumber satisfies the following properties. -/
def StarNumber (n : Int) : Id Unit :=
  sorry

/-- Specification: StarNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem StarNumber_spec (n : Int) :
    ⦃⌜True⌝⦄
    StarNumber n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

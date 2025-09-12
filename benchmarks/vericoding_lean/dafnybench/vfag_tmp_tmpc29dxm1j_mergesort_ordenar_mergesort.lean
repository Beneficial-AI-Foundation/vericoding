import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mezclar satisfies the following properties. -/
def mezclar (V : Array Int) : Id Unit :=
  sorry

/-- Specification: mezclar satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mezclar_spec (V : Array Int) :
    ⦃⌜True⌝⦄
    mezclar V
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mezclar satisfies the following properties. -/
def mezclar (V : array?<int>) : Id Unit :=
  sorry

/-- Specification: mezclar satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mezclar_spec (V : array?<int>) :
    ⦃⌜True⌝⦄
    mezclar V
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

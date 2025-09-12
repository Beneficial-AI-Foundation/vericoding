import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- multiply satisfies the following properties. -/
def multiply (m1 : array2<int>) : Id Unit :=
  sorry

/-- Specification: multiply satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem multiply_spec (m1 : array2<int>) :
    ⦃⌜True⌝⦄
    multiply m1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

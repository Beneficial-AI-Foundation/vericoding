import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- single satisfies the following properties. -/
def single (x : Array Int) : Id Unit :=
  sorry

/-- Specification: single satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem single_spec (x : Array Int) :
    ⦃⌜True⌝⦄
    single x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

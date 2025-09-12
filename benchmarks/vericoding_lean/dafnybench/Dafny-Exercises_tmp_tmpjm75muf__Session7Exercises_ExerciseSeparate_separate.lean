import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- separate satisfies the following properties. -/
def separate (v : Array Int) : Id Unit :=
  sorry

/-- Specification: separate satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem separate_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    separate v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

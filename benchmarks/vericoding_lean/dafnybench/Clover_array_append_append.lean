import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- append satisfies the following properties. -/
def append (a : Array Int) : Id Unit :=
  sorry

/-- Specification: append satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem append_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    append a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

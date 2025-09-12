import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- check satisfies the following properties. -/
def check (a : Array Int) : Id Unit :=
  sorry

/-- Specification: check satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem check_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    check a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- StartAndEndWithSameChar satisfies the following properties. -/
def StartAndEndWithSameChar (s : String) : Id Unit :=
  sorry

/-- Specification: StartAndEndWithSameChar satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem StartAndEndWithSameChar_spec (s : String) :
    ⦃⌜True⌝⦄
    StartAndEndWithSameChar s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

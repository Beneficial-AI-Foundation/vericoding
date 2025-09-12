import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- allDigits satisfies the following properties. -/
def allDigits (s : String) : Id Unit :=
  sorry

/-- Specification: allDigits satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem allDigits_spec (s : String) :
    ⦃⌜True⌝⦄
    allDigits s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

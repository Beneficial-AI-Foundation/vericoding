import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountDigits satisfies the following properties. -/
def CountDigits (s : String) : Id Unit :=
  sorry

/-- Specification: CountDigits satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountDigits_spec (s : String) :
    ⦃⌜True⌝⦄
    CountDigits s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

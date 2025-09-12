import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountUppercase satisfies the following properties. -/
def CountUppercase (s : String) : Id Unit :=
  sorry

/-- Specification: CountUppercase satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountUppercase_spec (s : String) :
    ⦃⌜True⌝⦄
    CountUppercase s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

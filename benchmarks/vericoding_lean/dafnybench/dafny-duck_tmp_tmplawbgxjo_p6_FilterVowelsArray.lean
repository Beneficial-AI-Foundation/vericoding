import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FilterVowelsArray satisfies the following properties. -/
def FilterVowelsArray (xs : array<char>) : Id Unit :=
  sorry

/-- Specification: FilterVowelsArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FilterVowelsArray_spec (xs : array<char>) :
    ⦃⌜True⌝⦄
    FilterVowelsArray xs
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

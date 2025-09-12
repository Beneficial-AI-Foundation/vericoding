import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindFirstRepeatedChar satisfies the following properties. -/
def FindFirstRepeatedChar (s : String) : Id Unit :=
  sorry

/-- Specification: FindFirstRepeatedChar satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindFirstRepeatedChar_spec (s : String) :
    ⦃⌜True⌝⦄
    FindFirstRepeatedChar s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindZero satisfies the following properties. -/
def FindZero (a : Array Int) : Id Unit :=
  sorry

/-- Specification: FindZero satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindZero_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    FindZero a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

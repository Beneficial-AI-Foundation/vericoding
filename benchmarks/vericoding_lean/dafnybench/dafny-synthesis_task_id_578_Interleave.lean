import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Interleave satisfies the following properties. -/
def Interleave (s1 : List Int) : Id Unit :=
  sorry

/-- Specification: Interleave satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Interleave_spec (s1 : List Int) :
    ⦃⌜True⌝⦄
    Interleave s1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- m3 satisfies the following properties. -/
def m3 (x : Int) : Id Unit :=
  sorry

/-- Specification: m3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem m3_spec (x : Int) :
    ⦃⌜True⌝⦄
    m3 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

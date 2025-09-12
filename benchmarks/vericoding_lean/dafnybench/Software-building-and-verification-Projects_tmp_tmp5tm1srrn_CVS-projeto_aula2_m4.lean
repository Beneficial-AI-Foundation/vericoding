import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- m4 satisfies the following properties. -/
def m4 (x : Int) : Id Unit :=
  sorry

/-- Specification: m4 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem m4_spec (x : Int) :
    ⦃⌜True⌝⦄
    m4 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

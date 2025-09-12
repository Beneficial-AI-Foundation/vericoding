import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mroot2 satisfies the following properties. -/
def mroot2 (n : Int) : Id Unit :=
  sorry

/-- Specification: mroot2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mroot2_spec (n : Int) :
    ⦃⌜True⌝⦄
    mroot2 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

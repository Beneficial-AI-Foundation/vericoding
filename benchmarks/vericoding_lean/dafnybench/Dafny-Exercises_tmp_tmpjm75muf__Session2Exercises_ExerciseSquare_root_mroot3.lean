import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mroot3 satisfies the following properties. -/
def mroot3 (n : Int) : Id Unit :=
  sorry

/-- Specification: mroot3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mroot3_spec (n : Int) :
    ⦃⌜True⌝⦄
    mroot3 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

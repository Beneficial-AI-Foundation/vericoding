import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mroot1 satisfies the following properties. -/
def mroot1 (n : Int) : Id Unit :=
  sorry

/-- Specification: mroot1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mroot1_spec (n : Int) :
    ⦃⌜True⌝⦄
    mroot1 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

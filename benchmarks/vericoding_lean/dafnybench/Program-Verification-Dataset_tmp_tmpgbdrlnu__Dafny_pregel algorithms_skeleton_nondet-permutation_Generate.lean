import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Generate satisfies the following properties. -/
def Generate (n : Int) : Id Unit :=
  sorry

/-- Specification: Generate satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Generate_spec (n : Int) :
    ⦃⌜True⌝⦄
    Generate n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

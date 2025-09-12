import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Guess satisfies the following properties. -/
def Guess (g : Int) : Id Unit :=
  sorry

/-- Specification: Guess satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Guess_spec (g : Int) :
    ⦃⌜True⌝⦄
    Guess g
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

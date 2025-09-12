import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Peek satisfies the following properties. -/
def Peek (elem : Int) : Id Unit :=
  sorry

/-- Specification: Peek satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Peek_spec (elem : Int) :
    ⦃⌜True⌝⦄
    Peek elem
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

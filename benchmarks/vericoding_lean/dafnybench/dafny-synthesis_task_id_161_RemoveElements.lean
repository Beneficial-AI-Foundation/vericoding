import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RemoveElements satisfies the following properties. -/
def RemoveElements (a : Array Int) : Id Unit :=
  sorry

/-- Specification: RemoveElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RemoveElements_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    RemoveElements a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

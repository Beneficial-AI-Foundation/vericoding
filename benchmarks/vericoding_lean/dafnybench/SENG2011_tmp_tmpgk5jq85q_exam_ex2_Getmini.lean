import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Getmini satisfies the following properties. -/
def Getmini (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Getmini satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Getmini_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Getmini a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

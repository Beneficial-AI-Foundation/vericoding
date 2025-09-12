import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- M satisfies the following properties. -/
def M (x : Int) : Id Unit :=
  sorry

/-- Specification: M satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem M_spec (x : Int) :
    ⦃⌜True⌝⦄
    M x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

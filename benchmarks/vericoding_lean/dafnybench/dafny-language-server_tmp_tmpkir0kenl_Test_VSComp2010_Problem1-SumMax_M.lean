import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- M satisfies the following properties. -/
def M (N : Int) : Id Unit :=
  sorry

/-- Specification: M satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem M_spec (N : Int) :
    ⦃⌜True⌝⦄
    M N
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

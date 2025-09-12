import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Pop satisfies the following properties. -/
def Pop (elem : Int) : Id Unit :=
  sorry

/-- Specification: Pop satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Pop_spec (elem : Int) :
    ⦃⌜True⌝⦄
    Pop elem
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

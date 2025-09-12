import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Fact satisfies the following properties. -/
def Fact (x : Int) : Id Unit :=
  sorry

/-- Specification: Fact satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Fact_spec (x : Int) :
    ⦃⌜True⌝⦄
    Fact x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

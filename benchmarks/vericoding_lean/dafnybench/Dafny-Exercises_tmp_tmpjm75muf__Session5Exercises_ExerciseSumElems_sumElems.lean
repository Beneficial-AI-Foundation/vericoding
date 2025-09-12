import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sumElems satisfies the following properties. -/
def sumElems (v : Array Int) : Id Unit :=
  sorry

/-- Specification: sumElems satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sumElems_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    sumElems v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

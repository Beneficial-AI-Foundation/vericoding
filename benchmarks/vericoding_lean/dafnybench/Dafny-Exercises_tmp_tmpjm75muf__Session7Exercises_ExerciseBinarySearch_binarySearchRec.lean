import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- binarySearchRec satisfies the following properties. -/
def binarySearchRec (v : Array Int) : Id Unit :=
  sorry

/-- Specification: binarySearchRec satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem binarySearchRec_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    binarySearchRec v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

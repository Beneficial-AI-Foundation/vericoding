import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- insert satisfies the following properties. -/
def insert (item : Int) : Id Unit :=
  sorry

/-- Specification: insert satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem insert_spec (item : Int) :
    ⦃⌜True⌝⦄
    insert item
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

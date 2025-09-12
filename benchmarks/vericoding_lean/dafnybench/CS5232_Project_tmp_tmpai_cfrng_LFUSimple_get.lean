import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- get satisfies the following properties. -/
def get (key : Int) : Id Unit :=
  sorry

/-- Specification: get satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem get_spec (key : Int) :
    ⦃⌜True⌝⦄
    get key
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

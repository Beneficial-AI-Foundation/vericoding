import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- main satisfies the following properties. -/
def main (x : Int) : Id Unit :=
  sorry

/-- Specification: main satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem main_spec (x : Int) :
    ⦃⌜True⌝⦄
    main x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

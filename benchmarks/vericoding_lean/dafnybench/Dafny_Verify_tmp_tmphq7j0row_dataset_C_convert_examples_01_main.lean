import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- main satisfies the following properties. -/
def main (t1 : Int) : Id Unit :=
  sorry

/-- Specification: main satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem main_spec (t1 : Int) :
    ⦃⌜True⌝⦄
    main t1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

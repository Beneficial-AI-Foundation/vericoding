import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- main satisfies the following properties. -/
def main (n : Int) : Id Unit :=
  sorry

/-- Specification: main satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem main_spec (n : Int) :
    ⦃⌜True⌝⦄
    main n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

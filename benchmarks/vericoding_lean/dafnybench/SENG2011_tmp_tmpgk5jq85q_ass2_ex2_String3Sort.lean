import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- String3Sort satisfies the following properties. -/
def String3Sort (a : String) : Id Unit :=
  sorry

/-- Specification: String3Sort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem String3Sort_spec (a : String) :
    ⦃⌜True⌝⦄
    String3Sort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

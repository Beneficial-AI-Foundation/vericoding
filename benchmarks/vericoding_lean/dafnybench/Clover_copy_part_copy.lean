import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- copy satisfies the following properties. -/
def copy (src : Array Int) : Id Unit :=
  sorry

/-- Specification: copy satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem copy_spec (src : Array Int) :
    ⦃⌜True⌝⦄
    copy src
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

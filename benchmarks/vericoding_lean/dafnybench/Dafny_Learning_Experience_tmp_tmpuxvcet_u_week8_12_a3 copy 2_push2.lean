import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- push2 satisfies the following properties. -/
def push2 (element : T) : Id Unit :=
  sorry

/-- Specification: push2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem push2_spec (element : T) :
    ⦃⌜True⌝⦄
    push2 element
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

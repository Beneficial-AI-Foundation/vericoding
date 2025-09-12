import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- push1 satisfies the following properties. -/
def push1 (element : T) : Id Unit :=
  sorry

/-- Specification: push1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem push1_spec (element : T) :
    ⦃⌜True⌝⦄
    push1 element
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

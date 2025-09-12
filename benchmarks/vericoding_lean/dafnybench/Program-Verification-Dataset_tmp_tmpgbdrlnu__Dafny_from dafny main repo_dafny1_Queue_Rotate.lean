import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Enqueue satisfies the following properties. -/
def Enqueue (t : T) : Id Unit :=
  sorry

/-- Specification: Enqueue satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Enqueue_spec (t : T) :
    ⦃⌜True⌝⦄
    Enqueue t
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

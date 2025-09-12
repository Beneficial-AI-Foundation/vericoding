import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Dequeue satisfies the following properties. -/
def Dequeue (e : Int) : Id Unit :=
  sorry

/-- Specification: Dequeue satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Dequeue_spec (e : Int) :
    ⦃⌜True⌝⦄
    Dequeue e
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

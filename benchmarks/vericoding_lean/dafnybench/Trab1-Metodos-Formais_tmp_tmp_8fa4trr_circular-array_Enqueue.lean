import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Enqueue satisfies the following properties. -/
def Enqueue (e : Int) : Id Unit :=
  sorry

/-- Specification: Enqueue satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Enqueue_spec (e : Int) :
    ⦃⌜True⌝⦄
    Enqueue e
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

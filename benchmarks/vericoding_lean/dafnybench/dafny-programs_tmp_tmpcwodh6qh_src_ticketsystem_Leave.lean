import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AtomicStep satisfies the following properties. -/
def AtomicStep (p : Process) : Id Unit :=
  sorry

/-- Specification: AtomicStep satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AtomicStep_spec (p : Process) :
    ⦃⌜True⌝⦄
    AtomicStep p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

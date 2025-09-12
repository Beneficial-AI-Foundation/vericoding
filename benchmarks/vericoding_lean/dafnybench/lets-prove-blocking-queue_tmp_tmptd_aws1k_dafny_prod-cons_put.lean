import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- put satisfies the following properties. -/
def put (p : Process) : Id Unit :=
  sorry

/-- Specification: put satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem put_spec (p : Process) :
    ⦃⌜True⌝⦄
    put p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks

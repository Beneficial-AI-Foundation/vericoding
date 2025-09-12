import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mcountEven satisfies the following properties. -/
def mcountEven (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mcountEven satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mcountEven_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mcountEven v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
